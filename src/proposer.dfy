class Proposer<T(==)>
{
  var majority:  int; // half of assumed active acceptors
  var round:     int; // current and largest encountered round from acceptors
  var prepared:  seq<int>; // set of answered prepares
  // previously  set<int>;
  var value:     T; // own value or value of acceptor with largest round

  constructor () {}

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