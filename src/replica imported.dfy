module Proposer {
	class SingleProposer<T(==)>
	{
		var majority:  int; // half of assumed active acceptors
		var round:     int; // our current round
		var value:     T; // own value or value of acceptor with largest round
		var largest:   int; // largest encountered round from acceptors
		var prepared:  set<int>; // set of answered prepares
		// previously  set<int>; changed due to bug with Length operator

		ghost var acceptors: map<int, T>; // a map<round, value> of prepared acceptors

		constructor (rnd: int, val: T)
			modifies this;
			ensures value == val;
			ensures valid();
		{
			majority  := 0;
			round     := rnd;
			value     := val;
			largest   := -1;
			acceptors := map[];
		}

		method Promise(id: int, acp_round: int, acp_value: T)
			returns (ok: bool, large: int, val: T)
			requires valid();
			// acceptors with equal round have equal value
			requires (acp_round == largest ==> acp_value == value)
				&& (acp_round in acceptors ==> acceptors[acp_round] == acp_value);
			modifies this;
			ensures  valid();
			ensures  id in prepared && large == round >= largest >= acp_round;
			// acceptors with equal round have equal value
			ensures  (acp_round == largest ==> acp_value == value)
				&& (acp_round in acceptors ==> acceptors[acp_round] == acp_value);
			// majority implies no accepted round is > largest encountered
			ensures  ok ==> (forall rnd :: rnd in acceptors ==> (
				rnd <= largest
			));
		{
			// log response from acceptor
			prepared  := prepared + {id};
			acceptors := acceptors[acp_round := acp_value]; // update ghost

			// Any prior accepted proposals? adopt round and value
			if largest < acp_round {
				largest := acp_round;
				value   := acp_value;
			}
			// due to round in sent prepare messages, pick the highest round
			if round < largest { round := largest; }

			ok := Evaluate_majority();
			return ok, round, value;
		}

		method Evaluate_majority() returns (ok: bool)
		{
			// got required majority of acceptors?
			if |prepared| >= majority {
				// TODO: store state
				return true;
			}
			return false;
		}

		method Reconfigure(num_acceptors: int)
			returns (ok: bool, rnd: int, val: T)
			requires valid();
			modifies this;
			ensures valid();
		{
			majority := num_acceptors/2 + 1;
			// re-evaluate |prepared| because we might NOT get more promises!
			ok := Evaluate_majority();
			// due to round in sent prepare messages, pick the highest round
			if round < largest { return ok, largest, value; }
			else { return ok, round, value; }
		}

		method SetMajority(maj: int)
			requires valid();
			modifies this;
			ensures  valid();
		{ majority := maj; }

		predicate valid()
			reads this;
		{
			// no promised acceptor's round is larger than ours
			(forall rnd :: rnd in acceptors ==> rnd <= round)
			// acceptors with equal round have equal value
			&& (largest in acceptors ==> acceptors[largest] == value)
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
		  then acp.round == round == promise && acp.value == value
		  else round < promise;
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
		var rnd:      int; // the highest encountered round number
		var val:      T;
		var accepted: set<int>; // set of acceptors that share current value
		// previously map<T, set<int>>; // accepted values mapping sets of acceptors that share it

		constructor () {}

		method Learn(id: int, acp_rnd: int, acp_val: T) returns (learned: bool, ret: T)
			modifies this;
			ensures rnd >= acp_rnd && if acp_val == val
				then id in accepted && (if learned then |accepted| >= majority else true)
				else true;
		{
			// are we not up to date?
			if acp_rnd > rnd {
				rnd := acp_rnd;
				// if new acp_val, out with the old
				if acp_val != val {
					val      := acp_val;
					accepted := {};
				}
			}
			// does the acceptor agree?
			if acp_val == val {
				// add acceptor to set
				accepted := accepted + {id};
				// do we have a majority?
				if |accepted| >= majority { return true, acp_val; }
				assert id in accepted;
			}
			return false, acp_val;
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
			ensures proposer == null || proposer.valid();
		{
			consensus := 0;
			var state_pro := false; // the state of this.proposer
			var state_acp := false; // the state of this.acceptor
			// false ==> null, true ==> valid
			this.self := self;
			this.val  := val;
			if ( roles >= 100 ) {
				proposer := new SingleProposer<T>( -1, val );
				state_pro := true;
				assert proposer.valid();
			}
			assert acceptor == null;
			var roles := roles % 100;
			if ( roles >= 10 ) {
				acceptor := new SingleAcceptor<T>( val );
				state_acp := true;
				assert acceptor != null && acceptor.valid();
				AddAcceptor( id, self, state_pro, state_acp );
				assert acceptor != null && acceptor.valid();
			}
			assert proposer == null || proposer.valid();
			roles := roles % 10;
			if (roles >= 1) {
				learner := new SingleLearner<T>();
				AddLearner( id, self, state_acp );
			}
		}

		method Promise(id: int, acp_round: int, acp_value: T)
			returns (ok: bool, largest: int, val: T)
			requires valid( proposer != null, acceptor != null);
			requires proposer != null ==> (
				proposer.valid()
				// acceptors with equal round have equal value
				&& (acp_round == proposer.largest ==> acp_value == proposer.value)
				&& (acp_round in proposer.acceptors ==> proposer.acceptors[acp_round] == acp_value)
			);
			modifies this.proposer;
			ensures  proposer == null || ok ==> proposer.round >= acp_round;
			ensures  valid( proposer != null, acceptor != null);
		{
			ok, largest, val := false, -1, acp_value;
			if proposer != null {
				ok, largest, val := proposer.Promise(id, acp_round, acp_value);
				assert ok ==> largest >= acp_round;
			}
			return ok, largest, val;
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
			// the final proof
			ensures if learned
			  then consensus >= majority
			  else consensus < majority;
		{
			if learner != null {
				learned, ret := learner.Learn(id, round, value);
			}
		}

		method AddAcceptor(id: int, addr: EndPoint, state_pro: bool, state_acp: bool)
			requires valid(state_pro, state_acp);
			modifies this, this.proposer, this.learner;
			ensures  valid(state_pro, state_acp);
		{
			acceptors := acceptors[id := addr];
			Configure( |acceptors|, state_pro, state_acp );
		}

		method AddLearner(id: int, addr: EndPoint, state_acp: bool)
			requires if state_acp
				then acceptor != null && acceptor.valid()
				else acceptor == null;
			modifies this;
			ensures  if state_acp
				then acceptor != null && acceptor.valid()
				else acceptor == null;
		{ learners := learners[id := addr]; }

		method Configure(num_acps: int, state_pro: bool, state_acp: bool)
			requires valid(state_pro, state_acp);
			modifies this, this.proposer, this.learner;
			ensures  valid(state_pro, state_acp);
		{
			this.majority := num_acps/2 + 1;
			if state_pro {
				proposer.SetMajority( majority );
			}
			// TODO: re-evaluate proposer's |prepared| because we might not get more promises!
			if (learner  != null) {
				learner.majority  := this.majority;
			}
		}

		predicate valid(state_pro: bool, state_acp: bool)
			reads this, this.proposer, this.acceptor,
				if this.acceptor != null then this.acceptor.accepted else null;
		{
			(if state_pro
				then proposer != null && proposer.valid()
				else proposer == null)
			&& (if state_acp
				then acceptor != null && acceptor.valid()
				else acceptor == null)
		}
	}
}