/**************************************--**************************************\
|*                                                                            *|
|*                                   PAXOS                                    *|
|*                                                                            *|
\**************************************--**************************************/
// author: Joakim Hagen
// modified: 2015-02-25
// columnwidth: 80

class DummyNetwork
{
  var interfaces: map<int, Interface>;
  var droprate:   int;

  method Promise(dest_ID: int, source_ID: int, group_ID: int, slot_ID: int,
    round: int, acceptedround: int, acceptedval: int)
    requires valid(this);
  {
    if (dest_ID in this.interfaces) {
      this.interfaces[dest_ID].Recieve_Promise(source_ID, group_ID, slot_ID,
        round, acceptedround, acceptedval);
    }
  }

  method Prepare(dest_ID: int, source_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int)
    requires valid(this);
  {
    if (dest_ID in this.interfaces) {
      this.interfaces[dest_ID].Recieve_Prepare(source_ID, group_ID, slot_ID,
        round, value);
    }
  }

  method Accept(dest_ID: int, source_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int)
    requires valid(this);
  {
    if (dest_ID in this.interfaces) {
      this.interfaces[dest_ID].Recieve_Accept(source_ID, group_ID, slot_ID,
        round, value);
    }
  }

  method Learn(dest_ID: int, source_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int)
    requires valid(this);
  {
    if (dest_ID in this.interfaces) {
      this.interfaces[dest_ID].Recieve_Learn(source_ID, group_ID, slot_ID,
        round, value);
    }
  }

  static predicate valid(net: DummyNetwork)
    reads net;
  {
    net != null
    // for all interfaces
    && forall k :: k in net.interfaces ==> Interface.valid(net.interfaces[k])
  }
}

class Interface // singleton
{
  var net:        DummyNetwork;
  var machine_ID: int; // A unique pseudo-random ID
  var groups:     map<int, Group>; // groups we participate in

  constructor Init(net: DummyNetwork, id: int)
    requires DummyNetwork.valid(net);
    ensures  this.net == net;
  {
    this.net        := net;
    this.machine_ID := id;
    this.groups     := map[];
  }

  // INSIDE
  method Promise(dest_ID: int, group_ID: int, slot_ID: int,
    round: int, acceptedround: int, acceptedval: int)
    requires DummyNetwork.valid(this.net);
  {
    this.net.Promise(dest_ID, this.machine_ID, group_ID, slot_ID,
      round, acceptedround, acceptedval);
  }

  method Prepare(dest_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int)
    requires DummyNetwork.valid(this.net);
  {
    this.net.Prepare(dest_ID, this.machine_ID, group_ID, slot_ID,
      round, value);
  }

  method Accept(dest_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int)
    requires DummyNetwork.valid(this.net);
  {
    this.net.Accept(dest_ID, this.machine_ID, group_ID, slot_ID,
      round, value);
  }

  method Learn(dest_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int)
    requires DummyNetwork.valid(this.net);
  {
    this.net.Learn(dest_ID, this.machine_ID, group_ID, slot_ID,
      round, value);
  }

  // OUTSIDE
  method Recieve_Propose(source_ID: int, group_ID: int, slot_ID: int,
    value: int)
    requires DummyNetwork.valid(this.net);
  {
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
    requires DummyNetwork.valid(this.net);
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
    round: int, value: int)
    requires DummyNetwork.valid(this.net);
  {
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
    round: int, value: int)
    requires DummyNetwork.valid(this.net);
  {
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
    requires DummyNetwork.valid(this.net);
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

  // non-recursive validation predicate for testing mutually linked objects
  static predicate valid(intf: Interface)
    reads intf;
  {
    intf != null
    && intf.net != null
    // all groups are valid
    && forall g :: g in intf.groups ==> Group.valid(intf.groups[g])
  }
}

// TODO: reduce arguments machine_ID, group_ID, slot_ID, round, value to a
// single object (less copying)


/* StateMachine
 * keeps data about how to reach a replica. IP/ports/protocols/keys/etc.
 */
class StateMachine {}

class Group
{
  var interface: Interface; // singleton
  var ID:        int; // this group's group_ID

  var proposers: array<int>; // array of machine ID's
  var acceptors: array<int>;
  var learners:  array<int>;

  var local_proposers: map<int, Proposer>; // key is slot_ID
  var local_acceptors: map<int, Acceptor>;
  var local_learners:  map<int, Learner>;

  constructor Init(intf: Interface)
    requires Interface.valid(intf);
    modifies this;
    ensures  valid(this) && this.interface == intf;
  {
    this.interface := intf;

    this.proposers := new array<int>;
    this.acceptors := new array<int>;
    this.learners  := new array<int>;

    // TODO: regarding maps can't be null, do they need initialization?
    this.local_proposers := map[];
    this.local_acceptors := map[];
    this.local_learners  := map[];
  }

  method AddLocalProposer(pro: Proposer)
    requires valid(this) && Interface.valid(this.interface) && pro != null;
    modifies this;
    // we leave important objects in this unchanged
    ensures  valid(this) && Interface.valid(this.interface);
  {
    this.local_proposers := this.local_proposers[pro.slot_ID := pro];
  }

  method Prepare(slot_ID: int, round: int, value: int)
    requires valid(this) && Interface.valid(this.interface);
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
    requires valid(this) && Interface.valid(this.interface);
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
    requires valid(this)
    && Interface.valid(this.interface);
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

  static predicate valid(grp: Group)
    reads grp;
  {
    grp != null && grp.interface != null && grp.proposers != null
    && grp.acceptors != null && grp.learners != null
    && forall p :: p in grp.local_proposers ==> grp.local_proposers[p] != null
    && forall a :: a in grp.local_acceptors ==> grp.local_acceptors[a] != null
    && forall l :: l in grp.local_learners  ==> grp.local_learners[l]  != null
  }
}

class Proposer
{
  var interface: Interface; // singleton
  var group:     Group; // list participating members
  var slot_ID:   int; // unique slot identifier

  var round:     int; // current round
  var largest:   int; // largest encountered round from acceptors
  var value:     int; // own value or value of acceptor with largest round
  var promised:  map<int, bool>; // bitmap of answered promises
  var count:     int; // amount of responses received

  constructor Init(intf: Interface, grp: Group, id: int)
    requires Interface.valid(intf) && Group.valid(grp);
    modifies this;
    ensures  this.interface == intf && this.group == grp;
  {
    this.interface := intf;
    this.group     := grp;
    this.slot_ID   := id;

    this.round     := 0;
    this.largest   := 0;
    this.value     := value;
    this.promised  := map[];
    this.count     := 0;
  }

  method Propose(source_ID: int, value: int) {}

  /* can be called by a malicious proposer?
   * The Proposer receives a response from an Acceptor where the current round
   * is the highest encountered.
   */
  method Promise(source_ID: int, round: int, acceptedround: int,
    acceptedval: int)
    requires Interface.valid(this.interface) && Group.valid(this.group)
      && acceptedround <= round <= this.round;
    modifies this;
    // TODO: what about when we receive double answers?
    // we leave important objects in this unchanged
    ensures  Interface.valid(this.interface) && Group.valid(this.group)
      && this.largest < acceptedround ==> this.value == acceptedval;
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
  var interface:     Interface; // singleton
  var group:         Group; // list participating members
  var slot_ID:       int; // unique slot identifier

  var promise :      int;
  var acceptedround: int;
  var acceptedval:   int;


  constructor Init(intf: Interface, grp: Group, id: int)
    requires Interface.valid(intf) && Group.valid(grp);
    modifies this;
    ensures  this.interface == intf && this.group == grp;
  {
    this.interface     := intf;
    this.group         := grp;
    this.slot_ID       := id;

    this.promise       := 0;
    this.acceptedround := 0;
    this.acceptedval   := 0;
  }

  method Prepare(source_ID: int, round: int, value: int)
    requires Interface.valid(this.interface) && Group.valid(this.group);
    modifies this;
    // we leave important objects in this unchanged
    ensures  Interface.valid(this.interface) && Group.valid(this.group)
      && this.promise >= round;
  {
    // is the round equal or newer than our promise?
    if (round >= this.promise) {
      this.promise := round;
      this.interface.Promise(source_ID, this.group.ID, this.slot_ID,
        round, this.acceptedround, this.acceptedval);
    }
  }

  method Accept(source_ID: int, round: int, value: int)
    requires Interface.valid(this.interface) && Group.valid(this.group);
    modifies this;
    // we leave important objects in this unchanged
    ensures  Interface.valid(this.interface) && Group.valid(this.group)
      && (round >= this.promise && round != this.acceptedround) ==>
      this.promise == round;
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
  var interface: Interface; // singleton

  constructor Init(intf: Interface)
    requires Interface.valid(intf);
    modifies this;
    ensures  this.interface == intf;
  {
    this.interface := intf;
  }

  method Learn(source_ID: int, round: int, value: int)
    requires Interface.valid(this.interface);
  {
    this.interface.EventLearn(round, value);
  }
}


