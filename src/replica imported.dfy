module Proposer {
	class SingleProposer<T(==)>
	{
		var majority:  int; // half of assumed active acceptors
		var round:     int; // current and largest encountered round from acceptors
		var prepared:  seq<int>; // set of answered prepares
		// previously  set<int>;
		var value:     T; // own value or value of acceptor with largest round

		constructor (rnd: int, val: T)
			modifies this;
			ensures value == val;
		{
			majority := 0;
			round    := rnd;
			value    := val;
		}

		method Promise(id: int, acp_round: int, acp_value: T)
			returns (largest: int, val: T)
			requires true;
			modifies this;
			ensures round >= acp_round;
		{
			// log response from acceptor
			prepared := prepared + [id];
			// previously  prepared := prepared + {id};
			// were there any prior proposals?
			if round < acp_round {
				value := acp_value;
				round := acp_round;
			}
			assert round >= acp_round;
			largest, val := Evaluate_majority();
			return largest, val;
		}

		method Evaluate_majority() returns (rnd: int, val: T)
		{
			// got required majority of acceptors?
			if |prepared| >= majority {
				// TODO: store state
				return round, value;
			}
			// else return nothing? 0, 0? 0, null?
		}

		method Configure(num_acceptors: int)
			returns (rnd: int, val: T)
			modifies this;
		{
			majority := num_acceptors/2 + 1;
			// re-evaluate |prepared| because we might not get more promises!
			rnd, val := Evaluate_majority();
			return rnd, val;
		}
	}
}

module Acceptor {
	class SingleAcceptor<T(==)>
	{
	  var promise:  int;
	  var accepted: Accepted<T>;

	  constructor (value: T)
		modifies this;
		ensures valid();
	  {
		promise  := 0;
		accepted := new Accepted(value);
	  }

	  method Prepare(round: int, value: T) returns (acp: Accepted<T>)
		requires valid();
		modifies this;
		ensures valid() && if acp != null
		  then promise == round > acp.round
		  else promise >= round;
	  {
		// is the round at least as new as our promise
		// and we have not already accepted it?
		if round >= promise && round != accepted.round {
		  promise := round;
		  // TODO: store state?
		  acp := accepted;
		}
		acp := null;
	  }

	  method Accept(round: int, value: T) returns (acp: Accepted<T>)
		requires valid();
		modifies this, accepted;
		ensures valid() && promise >= round && if acp != null
		  then acp.round == round && acp.value == value
		  else true;
	  {
		// is the round at least as new as our promise?
		if round >= promise {
		  promise        := round;
		  accepted.round := round;
		  accepted.value := value;
		  // TODO: store state
		  acp := accepted;
		}
		acp := null;
	  }

	  method Get() returns (rnd: int, acp: int, val: T)
		requires valid();
	  {
		rnd := promise;
		acp := accepted.round;
		val := accepted.value;
	  }

	  predicate valid()
		reads this, accepted;
	  { accepted != null && promise >= accepted.round }
	}

	class Accepted<T(==)>
	{
	  var round: int;
	  var value: T;

	  constructor (val: T)
		modifies this;
		ensures round == 0; // yes, this has to be explicitly stated!
	  { round := 0; value := val; }
	}
}

module Learner {
	class SingleLearner<T(==)>
	{
	  var majority: int; // half of assumed active acceptors
	  var current:  int; // the highest encountered round number
	  var accepted: map<T, seq<int>>; // accepted values mapping sets of acceptors that share it
	  // previously map<T, set<int>>;

	  constructor () {}

	  method Learn(id: int, round: int, value: T) returns (learned: bool, ret: T)
		modifies this;
		ensures current >= round && if round == current
		  then value in accepted && (if learned then |accepted[value]| >= majority else true)
		  else true;
	  {
		// is the acceptor up to date?
		if round > current {
		  current := round;
		  accepted := map[]; // new boys in town. out with the old
		}
		if round == current {
		  // add acceptor to set
		  if value !in accepted {
			// this is the first occurrance of value
			// accepted[value] := {id}
			accepted := accepted[ value := [id] ];
		  } else {
			// value already has a set. update with old set union {id}
			// accepted[value] += {id}
			accepted := accepted[ value := accepted[value] + [id] ];
		  }
		  // do we have a majority?
		  if |accepted[value]| >= majority {
			// yay
			return true, value;
		  }
		  assert value in accepted;
		}
		return false, value;
	  }
	}
}

module Replica {
	import opened Proposer
	import opened Acceptor
	import opened Learner

	trait EndPoint {
		function Equals(other: EndPoint): bool
			reads this;
			ensures this == other;
	}

	class Replica<T(==), EndPoint(==)> {

		var self:      EndPoint;
		var val:       T;
		var consensus: int;
		var majority:  int;
		var proposer:  SingleProposer<T>;
		var acceptor:  SingleAcceptor<T>;
		var learner:   SingleLearner<T>;
		var acceptors: map<int, EndPoint>;
		var learners:  map<int, EndPoint>;

		ghost var ghostacp: map<int, SingleAcceptor<T>>;

		constructor (id: int, roles: int, val: T, self: EndPoint)
		// roles are bitpattern [p.a.l] e.g 111 for all roles
			requires this.proposer == null && this.acceptor == null && this.learner == null;
			modifies this, this.proposer, this.learner;
			ensures acceptor == null || acceptor.valid();
		{
			consensus := 0;
			var state := 0; // the state of this.acceptor. 0=null, 1=valid
			this.self := self;
			this.val  := val;
			if ( roles >= 100 ) {
				proposer := new SingleProposer<T>( -1, val );
			}
			assert acceptor == null;
			var roles := roles % 100;
			if ( roles >= 10 ) {
				acceptor := new SingleAcceptor<T>( val );
				state := 1;
				assert acceptor != null && acceptor.valid();
				AddAcceptor( id, self, state );
				assert acceptor != null && acceptor.valid();
			}
			roles := roles % 10;
			if (roles >= 1) {
				learner := new SingleLearner<T>();
				AddLearner( id, self, state );
			}
		}

		method Promise(id: int, acp_round: int, acp_value: T)
			returns (largest: int, val: T)
			modifies this.proposer;
			ensures proposer == null || proposer.round >= acp_round;
		{
			if proposer != null {
				var largest, val := proposer.Promise(id, acp_round, acp_value);
				return largest, val;
			}
		}

		method Prepare(round: int, value: T) returns (acp: Accepted<T>)
			requires acceptor == null || acceptor.valid();
			modifies this, this.acceptor;
			ensures acceptor == null || acceptor.promise >= round;
		{
			if acceptor != null {
				acp := acceptor.Prepare(round, value);
				if acp != null {
					this.val := acp.value;
				}
			}
		}

		method Accept(round: int, value: T) returns (acp: Accepted<T>)
			requires acceptor == null || acceptor.valid();
			modifies this, this.acceptor;
			modifies if this.acceptor != null then this.acceptor.accepted else null;
			ensures acceptor == null || acceptor.promise >= round;
		{
			if acceptor != null {
				acp := acceptor.Accept(round, value);
				if acp != null && acp.round > round {
					assert acp.round == round;
					assert acp.value == value;
					this.consensus := this.consensus + 1;
				}
			}
		}

		method Learn(id: int, round: int, value: T) returns (learned: bool, ret: T)
			modifies this.learner;
			ensures if learned
			  then consensus >= majority
			  else consensus < majority;
		{
			if learner != null {
				learned, ret := learner.Learn(id, round, value);
			}
		}

		method AddAcceptor(id: int, addr: EndPoint, state: int)
			requires (state == 0 && acceptor == null)
			      || (state == 1 && acceptor != null && acceptor.valid());
			modifies this, this.proposer, this.learner;
			ensures  (state == 0 && acceptor == null)
			      || (state == 1 && acceptor != null && acceptor.valid());
		{
			ghost var state2 := false;
			if acceptor != null { ghost var state2 := true; }
			acceptors := acceptors[id := addr];
			Configure( |acceptors|, state );
			// add to ghost map
			var acp := new SingleAcceptor<T>( this.val );
			ghostacp := ghostacp[id := acp];
			if state2 { assert acceptor.valid(); }
		}

		method AddLearner(id: int, addr: EndPoint, state: int)
			requires (state == 0 && acceptor == null)
			      || (state == 1 && acceptor != null && acceptor.valid());
			modifies this;
			ensures  (state == 0 && acceptor == null)
			      || (state == 1 && acceptor != null && acceptor.valid());
		{ learners := learners[id := addr]; }

		method Configure(num_acps: int, state: int)
			requires (state == 0 && acceptor == null)
			      || (state == 1 && acceptor != null && acceptor.valid());
			modifies this, this.proposer, this.learner;
			ensures  (state == 0 && acceptor == null)
			      || (state == 1 && acceptor != null && acceptor.valid());
		{
			this.majority := num_acps/2 + 1;
			if (proposer != null) { proposer.majority := this.majority; }
			// TODO: re-evaluate proposer's |prepared| because we might not get more promises!
			if (learner  != null) { learner.majority  := this.majority; }
		}
	}
}