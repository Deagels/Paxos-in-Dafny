class Learner
{
  var majority: int; // half of assumed active acceptors
  var current:  int; // the highest encountered round number
  var accepted: map<int, set<int>>; // accepted values mapping sets of acceptors that share it

  constructor Init(id: int)
    modifies this;
  {
    this.current := 0;
  }

  method Learn(id: int, round: int, value: int) returns (val: int)
    modifies this;
  {
    // is the acceptor up to date?
    if round >= current {
      current := round;
      // add acceptor to set
      if value !in accepted {
        accepted := accepted[ value := {id} ];
      } else {
        accepted := accepted[ value := accepted[value] + {id} ];
      }
      // do we have a majority?
      if |accepted[value]| >= majority {
        // yay
      }
    }
    return 0;
  }
}