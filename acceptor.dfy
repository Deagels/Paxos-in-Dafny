class Acceptor<T(==)>
{
  var promise:  int;
  var accepted: Accepted<T>;

  constructor ()
    modifies this;
  { accepted := new Accepted(); }

  method Prepare(round: int, value: T) returns (acp: Accepted<T>)
	requires valid();
    modifies this;
	ensures valid() && promise >= round;
  {
    // is the round at least as new as our promise
	// and we have not already accepted it?
    if round >= promise && round != accepted.round {
      promise := round;
	  assert promise > accepted.round;
	  // TODO: store state?
      return accepted;
    }
	return null;
  }

  method Accept(round: int, value: T) returns (acp: Accepted<T>)
	requires valid();
    modifies this, accepted;
	ensures valid() && promise >= round;
  {
    // is the round at least as new as our promise?
    if round >= promise {
      promise       := round;
      accepted.round := round;
      accepted.value   := value;
	  // TODO: store state
	  return accepted;
    }
	return null;
  }

  method Get() returns (rnd: int, acp: int, val: T)
    requires valid();
  { return promise, accepted.round, accepted.value; }

  predicate valid()
    reads this, accepted;
  { accepted != null && promise >= accepted.round }
}

class Accepted<T(==)>
{
  var round: int;
  var value: T;

  constructor () {}
}