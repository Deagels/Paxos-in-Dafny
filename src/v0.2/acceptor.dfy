class Acceptor<T(==)>
{
  var promise:  int;
  var accepted: Accepted<T>;

  constructor (value: T)
    modifies this;
    ensures valid();
  {
    promise  := -1;
    accepted := new Accepted(value);
  }

  method Prepare(round: int, value: T) returns (ok: bool, acp: Accepted<T>)
    requires valid();
    modifies this;
  ensures valid() && promise >= round;
  {
    acp := accepted;
    ok  := false;
    // is the round at least as new as our promise
    // and we have not already accepted it?
    if round >= promise && round != accepted.round {
      promise := round;
      assert promise > accepted.round;
      // TODO: store state?
      ok := true;
    }
  }

  method Accept(round: int, value: T) returns (ok: bool, acp: Accepted<T>)
    requires valid();
    modifies this, accepted;
  ensures valid() && promise >= round;
  {
    acp := accepted;
    ok  := false;
    // is the round at least as new as our promise?
    if round >= promise {
      promise         := round;
      accepted.round  := round;
      accepted.value  := value;
      // TODO: store state
      ok := true;
    }
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
    ensures round == -1; // yes, this has to be explicitly stated!
  { round := -1; value := val; }
}