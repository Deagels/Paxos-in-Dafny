/**************************************--**************************************\
|*                                                                            *|
|*                                   PAXOS                                    *|
|*                                                                            *|
\**************************************--**************************************/
// author: Joakim Hagen
// modified: 2015-02-23
// columnwidth: 80

class Interface // singleton
{
  var others:     map<int, Interface>;
  var dropper:    Dropper;

  var machine_ID: int; // A unique pseudorandom ID
  var groups:     map<int, Group>; // groups we participate in

  constructor Init(id: int)
  {
    this.others     := map[];
    this.dropper    := new Dropper;
    this.machine_ID := id;
    this.groups     := map[];
  }

  // INSIDE
  method Promise(dest_ID: int, group_ID: int, slot_ID: int,
    round: int, acceptedround: int, acceptedval: int)
    // no elements in others are null
    requires forall k :: k in this.others ==> this.others[k] != null;
  {
    if (dest_ID in this.others) {
      this.others[dest_ID].Recieve_Promise(this.machine_ID, group_ID, slot_ID,
        round, acceptedround, acceptedval);
    }
    // here is where the client program should generate a package and send to
    // another machine
  }

  method Prepare(dest_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int)
    // no elements in others are null
    requires forall k :: k in this.others ==> this.others[k] != null;
  {
    if (dest_ID in this.others) {
      this.others[dest_ID].Recieve_Prepare(this.machine_ID, group_ID, slot_ID,
        round, value);
    }
  }

  method Accept(dest_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int)
    // no elements in others are null
    requires forall k :: k in this.others ==> this.others[k] != null;
  {
    if (dest_ID in this.others) {
      this.others[dest_ID].Recieve_Accept(this.machine_ID, group_ID, slot_ID,
        round, value);
    }
  }

  method Learn(dest_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int)
    // no elements in others are null
    requires forall k :: k in this.others ==> this.others[k] != null;
  {
    if (dest_ID in this.others) {
      this.others[dest_ID].Recieve_Learn(this.machine_ID, group_ID, slot_ID,
        round, value);
    }
  }

  // OUTSIDE
  method Recieve_Propose(source_ID: int, group_ID: int, slot_ID: int,
    value: int) {
    // Are we a member of this group & have a proposer for this slot?
    if (group_ID in this.groups) {
      assert this.groups[group_ID] != null;
      var local := this.groups[group_ID].local_proposers;
      if (slot_ID in local) {
        assert local[slot_ID] != null;
        local[slot_ID].Propose(source_ID, value);
      } // TODO: else create new slot??
    }
  }

  method Recieve_Promise(source_ID: int, group_ID: int, slot_ID: int,
    round: int, acceptedround: int, acceptedval: int)
    // no elements in groups or local_proposers are null
    requires forall k :: k in this.groups ==> (
      this.groups[k] != null && forall l :: l in this.groups[k].local_proposers
      ==> this.groups[k].local_proposers[l] != null
    );
  {
    // Are we a member of this group & have a proposer for this slot?
    if (group_ID in this.groups) {
      var local := this.groups[group_ID].local_proposers;
      if (slot_ID in local) {
        local[slot_ID].Promise(source_ID, round, acceptedround, acceptedval);
      }
    }
  }

  method Recieve_Prepare(source_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int) {
    // Are we a member of this group & have an acceptor for this slot?
    if (group_ID in this.groups) {
      assert this.groups[group_ID] != null;
      var local := this.groups[group_ID].local_acceptors;
      if (slot_ID in local) {
        assert local[slot_ID] != null;
        local[slot_ID].Prepare(source_ID, round, value);
      }
    }
  }

  method Recieve_Accept(source_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int) {
    // Are we a member of this group & have an acceptor for this slot?
    if (group_ID in this.groups) {
      assert this.groups[group_ID] != null;
      var local := this.groups[group_ID].local_acceptors;
      if (slot_ID in local) {
        assert local[slot_ID] != null;
        local[slot_ID].Accept(source_ID, round, value);
      }
    }
  }

  method Recieve_Learn(source_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int)
    // no elements in groups or local_learners are null
    requires forall k :: k in this.groups ==> (
      this.groups[k] != null && forall l :: l in this.groups[k].local_learners
      ==> this.groups[k].local_learners[l] != null
    );
  {
    // Are we a member of this group & have a learner for this slot?
    if (group_ID in this.groups) {
      var local := this.groups[group_ID].local_learners;
      if (slot_ID in local) {
        local[slot_ID].Learn(source_ID, round, value);
      }
    }
  }

  /* Store
   * This method is to be overridden by the client application in the effort
   * to provide safe storage of information to a non-volatile device.
   */
  method Store(value: int) {}

  method EventLearn(round: int, value: int) {}
}

// TODO: reduce arguments machine_ID, group_ID, slot_ID, round, value to a
// single object (less copying)


/* StateMachine
 * keeps data about how to reach a replica. IP/ports/protocols/keys/etc.
 */
class StateMachine {}

class Group
{
  var interface: Interface; // singelton
  var ID:        int; // this group's group_ID

  var proposers: array<int>; // array of machine ID's
  var acceptors: array<int>;
  var learners:  array<int>;

  var local_proposers: map<int, Proposer>; // key is slot_ID
  var local_acceptors: map<int, Acceptor>;
  var local_learners:  map<int, Learner>;

  constructor Init(interface: Interface)
    requires interface != null;
    modifies this;
    ensures  this.interface != null;
  {
    this.interface := interface;

    this.proposers := new array<int>;
    this.acceptors := new array<int>;
    this.learners  := new array<int>;

    this.local_proposers := map[];
    this.local_acceptors := map[];
    this.local_learners  := map[];
  }

  method AddLocalProposer(pro: Proposer)
    requires pro != null;
    modifies this;
  {
    this.local_proposers := this.local_proposers[pro.slot_ID := pro];
  }

  method Prepare(slot_ID: int, round: int, value: int)
    requires this.interface != null && this.acceptors != null;
  {
    var i := 0;
    var n := this.acceptors.Length;
    while (i < n)
      invariant 0 <= i <= n;
    {
      this.interface.Prepare(acceptors[i], this.ID, slot_ID, round, value);
      i := i + 1;
    }
  }

  method Accept(slot_ID: int, round: int, value: int)
    requires this.interface != null && this.acceptors != null;
  {
    var i := 0;
    var n := this.acceptors.Length;
    while (i < n)
      invariant 0 <= i <= n;
    {
      this.interface.Accept(acceptors[i], this.ID, slot_ID, round, value);
      i := i + 1;
    }
  }

  method Learn(slot_ID: int, round: int, value: int)
    requires this.interface != null && this.learners != null;
  {
    var i := 0;
    var n := this.learners.Length;
    while (i < n)
      invariant 0 <= i <= n;
    {
      this.interface.Learn(learners[i], this.ID, slot_ID, round, value);
      i := i + 1;
    }
  }
}

class Proposer
{
  var interface: Interface; // singelton
  var group:     Group; // list participating members
  var slot_ID:   int; // unique slot identifier

  var round:     int; // current round
  var largest:   int; // largerst encountered round from acceptors
  var value:     int; // own value or value of acceptor with largest round
  var promised:  map<int, bool>; // bitmap of answered promises
  var count:     int; // amount of responses received

  constructor Init(interface: Interface, group: Group, id: int)
    requires interface != null;
    modifies this;
    ensures  this.interface != null;
  {
    this.interface:= interface;
    this.group    := group;
    this.slot_ID  := id;

    this.round    := 0;
    this.largest  := 0;
    this.value    := value;
    this.promised := map[];
    this.count    := 0;
  }

  method Propose(source_ID: int, value: int) {}

  /* can be called by a malicious proposer?
   * The Proposer receives a response from an Acceptor where the current round
   * is the highest encountered.
   */
  method Promise(source_ID: int, round: int, acceptedround: int,
    acceptedval: int)
    requires source_ID in this.promised && this.interface != null
      && this.group != null && this.group.acceptors != null
      && acceptedround <= round <= this.round;
    modifies this;
    ensures  this.largest < acceptedround ==> this.value == acceptedval;
  {
    // not first response from acceptor?
    if (this.promised[source_ID]) { return; }
    this.promised := this.promised[source_ID := true];
    this.count    := this.count + 1; // +1 promise

    // were there any prior proposals?
    if (this.largest < acceptedround) {
      this.value   := acceptedval;
      this.largest := acceptedround;
    }

    // TODO: don't call Accept before all Prepares are sent!
    // got required majority of promises?
    if (this.count > this.group.acceptors.Length/2) {
      // TODO: store state
      this.interface.Accept(source_ID, this.group.ID, this.slot_ID,
        round, value);
    }
  }
}

class Acceptor
{
  var interface:     Interface; // singelton
  var group:         Group; // list participating members
  var slot_ID:       int; // unique slot identifier

  var promise :      int;
  var acceptedround: int;
  var acceptedval:   int;


  constructor Init(interface: Interface, group: Group, id: int)
    requires interface != null;
    modifies this;
    ensures  this.interface != null;
  {
    this.interface     := interface;
    this.group         := group;
    this.slot_ID       := id;

    this.promise       := 0;
    this.acceptedround := 0;
    this.acceptedval   := 0;
  }

  method Prepare(source_ID: int, round: int, value: int)
    requires this.interface != null && this.group != null;
    modifies this;
    ensures this.promise >= round;
  {
    // is the round equal or newer than our promise?
    if (round >= this.promise) {
      this.promise := round;
      this.interface.Promise(source_ID, this.group.ID, this.slot_ID,
        round, this.acceptedround, this.acceptedval);
    }
  }

  method Accept(source_ID: int, round: int, value: int)
    requires this.group != null;
    modifies this;
  {
    // is the round at least as new as the promise
    if (round >= this.promise && round != this.acceptedround) {
      this.promise       := round;
      this.acceptedround := round;
      this.acceptedval   := value;
      this.group.Learn(slot_ID, round, value);
    }
  }
}

class Learner
{
  var interface: Interface; // singelton

  constructor Init(interface: Interface, group: Group, id: int)
    requires interface != null;
    modifies this;
    ensures  this.interface != null;
  {
    this.interface := interface;
  }

  method Learn(source_ID: int, round: int, value: int)
    requires this.interface != null;
  {
    this.interface.EventLearn(round, value);
  }
}

class Dropper
{
  var droprate: int;

  method Send(val: int) {}

  function Proceed(): bool { true }
}