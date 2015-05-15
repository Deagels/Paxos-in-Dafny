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