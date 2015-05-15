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