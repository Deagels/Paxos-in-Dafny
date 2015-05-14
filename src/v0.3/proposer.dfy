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
