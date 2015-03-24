class Learner<T(==)>
{
  var majority: int; // half of assumed active acceptors
  var current:  int; // the highest encountered round number
  var accepted: map<T, seq<int>>; // accepted values mapping sets of acceptors that share it
  // previously map<T, set<int>>;

  constructor ()
    modifies this;
  {
    majority := 0;
	current  := -1;
  }

  method Learn(id: int, round: int, value: T) returns (learned: bool, ret: T)
    modifies this;
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
    }
    return false, value;
  }

  method Configure(num_acceptors: int)
    modifies this;
  {
    majority := num_acceptors/2 + 1;
	// re-evaluate?
  }
}