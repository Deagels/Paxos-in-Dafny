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