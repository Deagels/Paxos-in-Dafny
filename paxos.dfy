/**************************************--**************************************\
|*                                                                            *|
|*                                   PAXOS                                    *|
|*                                                                            *|
\**************************************--**************************************/
// author: Joakim Hagen
// modified: 2015-03-09
// columnwidth: 80

class DummyNetwork
{
  var interfaces: map<int, Interface>;

  method Promise(dest_ID: int, source_ID: int, group_ID: int, slot_ID: int,
    round: int, acceptedround: int, acceptedval: int)
    requires forall i :: i in this.interfaces ==> this.interfaces[i] != null;
  {
    if (dest_ID in this.interfaces) {
      this.interfaces[dest_ID].Recieve_Promise(source_ID, group_ID, slot_ID,
        round, acceptedround, acceptedval);
    }
  }

  method Prepare(dest_ID: int, source_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int)
    requires forall i :: i in this.interfaces ==> this.interfaces[i] != null;
  {
    if (dest_ID in this.interfaces) {
      this.interfaces[dest_ID].Recieve_Prepare(source_ID, group_ID, slot_ID,
        round, value);
    }
  }

  method Accept(dest_ID: int, source_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int)
    requires forall i :: i in this.interfaces ==> this.interfaces[i] != null;
  {
    if (dest_ID in this.interfaces) {
      this.interfaces[dest_ID].Recieve_Accept(source_ID, group_ID, slot_ID,
        round, value);
    }
  }

  method Learn(dest_ID: int, source_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int)
    requires forall i :: i in this.interfaces ==> this.interfaces[i] != null;
  {
    if (dest_ID in this.interfaces) {
      this.interfaces[dest_ID].Recieve_Learn(source_ID, group_ID, slot_ID,
        round, value);
    }
  }
}

class Interface // singleton
{
  var net:        DummyNetwork;
  var machine_ID: int; // A unique pseudo-random ID
  var groups:     map<int, Group>; // groups we participate in

  constructor Init(net: DummyNetwork, id: int)
    requires net != null
      && forall i :: i in net.interfaces ==> net.interfaces[i] != null;
    modifies this, net;
    ensures  this.valid() && forall i :: i in net.interfaces ==> net.interfaces[i] != null;
  {
    this.net        := net;
    this.machine_ID := id;
    this.groups     := map[];
    // add self to map of interfaces
    net.interfaces := net.interfaces[id := this];
  }

  // INSIDE
  method Promise(dest_ID: int, group_ID: int, slot_ID: int,
    round: int, acceptedround: int, acceptedval: int)
    requires this.valid();
  {
    this.net.Promise(dest_ID, this.machine_ID, group_ID, slot_ID,
      round, acceptedround, acceptedval);
  }

  method Prepare(dest_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int)
    requires this.valid();
  {
    this.net.Prepare(dest_ID, this.machine_ID, group_ID, slot_ID,
      round, value);
  }

  method Accept(dest_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int)
    requires this.valid();
  {
    this.net.Accept(dest_ID, this.machine_ID, group_ID, slot_ID,
      round, value);
  }

  method Learn(dest_ID: int, group_ID: int, slot_ID: int,
    round: int, value: int)
    requires this.valid();
  {
    this.net.Learn(dest_ID, this.machine_ID, group_ID, slot_ID,
      round, value);
  }

  // OUTSIDE
  method Recieve_Propose(source_ID: int, group_ID: int, slot_ID: int,
    value: int)
    requires this.valid()
      && forall i :: i in net.interfaces ==> net.interfaces[i] != null;
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
    requires this.valid()
      && forall i :: i in net.interfaces ==> net.interfaces[i] != null;
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
    requires this.valid()
      && forall i :: i in net.interfaces ==> net.interfaces[i] != null;
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
    requires this.valid()
      && forall i :: i in net.interfaces ==> net.interfaces[i] != null;
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
    requires this.valid()
      && forall i :: i in net.interfaces ==> net.interfaces[i] != null;
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

  function groups() : set<Group>
    reads this;
  { set g | g in this.groups :: this.groups[g] }

  function groupRead() : set<object>
    reads this;
  { set x | x in this.groups && this.groups[x] != null :: this.groups[x].read() }

  function flatten(nested: set<set<Group>>) : set<Group>
  { set x | forall y :: y in nested && x in y :: x }

  predicate valid()
    reads this;
    reads set g | g in this.groups :: this.groups[g];
    //reads set x | x in this.groups && this.groups[x] != null :: this.groups[x].valid;
    //reads set x | x in this.groups && this.groups[x] != null :: this.groups[x].valid.reads;
    //reads flatten(set x | x in this.groups && this.groups[x] != null :: this.groups[x].valid.reads());
    reads if 0 in this.groups && this.groups[0] != null then this.groups[0].valid.reads() else {};
    reads flatten.reads(set x | x in this.groups && this.groups[x] != null :: this.groups[x].read());
    reads flatten();
  {
    this.net != null
    // all groups are valid
    && forall g :: g in this.groups ==> (
      this.groups[g] != null && this.groups[g].valid()
      && this.groups[g].interface == this
    )
  }

  // non-recursive validation predicate for testing mutually linked objects
}

// TODO: reduce arguments machine_ID, group_ID, slot_ID, round, value to a
// single object (less copying)

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

  constructor (intf: Interface)
    requires intf != null && intf.valid()
      && forall i :: i in intf.net.interfaces ==> intf.net.interfaces[i] != null;
    modifies this, intf;
    ensures  this.valid()
      && this.interface.valid()
      && forall i :: i in this.interface.net.interfaces ==> this.interface.net.interfaces[i] != null;
  {
    this.interface := intf;

    this.proposers := new array<int>;
    this.acceptors := new array<int>;
    this.learners  := new array<int>;

    // TODO: regarding maps can't be null, do they need initialization?
    this.local_proposers := map[];
    this.local_acceptors := map[];
    this.local_learners  := map[];
    // add self to map of groups
    intf.groups := intf.groups[ID := this];
    assert intf == this.interface;
  }

  method Prepare(slot_ID: int, round: int, value: int)
    requires this.valid() && this.interface.valid();
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
    requires this.valid() && this.interface.valid();
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
    requires this.valid()
    && this.interface.valid();
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
  
  function read() : set<object>
    reads this, this.valid.reads();
  { this.valid.reads() }

  predicate valid()
    reads this,
      set p | p in this.local_proposers :: this.local_proposers[p],
      set a | a in this.local_acceptors :: this.local_acceptors[a],
      set l | l in this.local_learners :: this.local_learners[l];
  {
    this.interface != null
    && this.proposers != null
    && this.acceptors != null
    && this.learners  != null
    && forall p :: p in this.local_proposers ==>
      (this.local_proposers[p] != null && this.local_proposers[p].valid(this))
    && forall a :: a in this.local_acceptors ==>
      (this.local_acceptors[a] != null && this.local_acceptors[a].valid(this))
    && forall l :: l in this.local_learners ==>
      (this.local_learners[l] != null && this.local_learners[l].valid(this))
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

  constructor Init(grp: Group, id: int)
    requires grp != null && grp.valid()
      && grp.interface.valid()
      && forall i :: i in grp.interface.net.interfaces ==> grp.interface.net.interfaces[i] != null;
    modifies this, grp;
    ensures  this.group == grp && this.group.valid()
      && this.interface == grp.interface && this.interface.valid()
      && forall i :: i in this.interface.net.interfaces ==> this.interface.net.interfaces[i] != null;
  {
    this.interface := grp.interface;
    this.group     := grp;
    this.slot_ID   := id;

    this.round     := 0;
    this.largest   := 0;
    this.value     := value;
    this.promised  := map[];
    this.count     := 0;
    // add self to local_proposers
    grp.local_proposers := grp.local_proposers[id := this];
  }

  method Propose(source_ID: int, value: int) {}

  /* can be called by a malicious proposer?
   * The Proposer receives a response from an Acceptor where the current round
   * is the highest encountered.
   */
  method Promise(source_ID: int, round: int, acceptedround: int,
    acceptedval: int)
    requires this.group != null && this.group.valid()
      && this.interface != null && this.interface.valid()
      && forall i :: i in this.interface.net.interfaces ==> this.interface.net.interfaces[i] != null
      && acceptedround <= round <= this.round;
    modifies this;
    // TODO: what about when we receive double answers?
    // we leave important objects in this unchanged
    ensures  this.group != null && this.group.valid()
      && this.interface != null && this.interface.valid()
      && forall i :: i in this.interface.net.interfaces ==> this.interface.net.interfaces[i] != null
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
      assert this.group.valid()
        && this.interface.valid()
        && forall i :: i in this.interface.net.interfaces ==> this.interface.net.interfaces[i] != null;
      // TODO: store state
      this.interface.Accept(source_ID, this.group.ID, this.slot_ID,
        round, value);
    }
  }

  predicate valid(grp: Group)
    requires grp != null;
    reads this, grp;
  {
    this.group == grp
    && this.interface == grp.interface
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


  constructor Init(grp: Group, id: int)
    requires grp != null && grp.valid()
      && grp.interface.valid()
      && forall i :: i in grp.interface.net.interfaces ==> grp.interface.net.interfaces[i] != null;
    modifies this, grp;
    ensures  this.group == grp && this.group.valid()
      && this.interface == grp.interface && this.interface.valid()
      && forall i :: i in this.interface.net.interfaces ==> this.interface.net.interfaces[i] != null;
  {
    this.interface     := grp.interface;
    this.group         := grp;
    this.slot_ID       := id;

    this.promise       := 0;
    this.acceptedround := 0;
    this.acceptedval   := 0;

    assert grp.valid();
    assert this.group.valid();
    assert this.group == grp;
    assert this.interface == grp.interface;

    assert forall a :: a in grp.local_acceptors ==>
      grp.local_acceptors[a] != null;

    assert forall a :: a in grp.local_acceptors ==>
      grp.local_acceptors[a].group == grp;

    assert forall a :: a in grp.local_acceptors ==>
      grp.local_acceptors[a].interface == grp.interface;

    // add self to local_acceptors
    grp.local_acceptors := grp.local_acceptors[id := this];
  }

  method Prepare(source_ID: int, round: int, value: int)
    requires this.group != null && this.group.valid()
      && this.interface != null && this.interface.valid()
      && forall i :: i in this.interface.net.interfaces ==> this.interface.net.interfaces[i] != null;
    modifies this;
    // we leave important objects in this unchanged
    ensures  this.group != null && this.group.valid()
      && this.interface != null && this.interface.valid()
      && forall i :: i in this.interface.net.interfaces ==> this.interface.net.interfaces[i] != null
      && this.promise >= round;
  {
    // is the round equal or newer than our promise?
    if (round >= this.promise) {
      this.promise := round;
      assert this.group.valid()
        && this.interface.valid()
        && forall i :: i in this.interface.net.interfaces ==> this.interface.net.interfaces[i] != null;
      this.interface.Promise(source_ID, this.group.ID, this.slot_ID,
        round, this.acceptedround, this.acceptedval);
    }
  }

  method Accept(source_ID: int, round: int, value: int)
    requires this.group != null && this.group.valid()
      && this.interface != null && this.interface.valid()
      && forall i :: i in this.interface.net.interfaces ==> this.interface.net.interfaces[i] != null;
    modifies this;
    // we leave important objects in this unchanged
    ensures  this.group != null && this.group.valid()
      && this.interface != null && this.interface.valid()
      && forall i :: i in this.interface.net.interfaces ==> this.interface.net.interfaces[i] != null
      && (round >= this.promise && round != this.acceptedround) ==>
      this.promise == round;
  {
    // is the round at least as new as the promise
    if (round >= this.promise && round != this.acceptedround) {
      this.promise       := round;
      this.acceptedround := round;
      this.acceptedval   := value;
      assert this.group.valid()
        && this.interface.valid()
        && forall i :: i in this.interface.net.interfaces ==> this.interface.net.interfaces[i] != null
        && this.promise == round;
      this.group.Learn(slot_ID, round, value);
    }
  }

  predicate valid(grp: Group)
    requires grp != null;
    reads this, grp;
  {
    this.group == grp && this.interface == grp.interface
  }
}

class Learner
{
  var interface: Interface; // singleton

  constructor Init(grp: Group, id: int)
    requires grp != null && grp.valid()
      && grp.interface.valid()
      && forall i :: i in grp.interface.net.interfaces ==> grp.interface.net.interfaces[i] != null;
    modifies this, grp;
    ensures  grp != null && grp.valid()
      && this.interface != null && this.interface.valid()
      && forall i :: i in this.interface.net.interfaces ==> this.interface.net.interfaces[i] != null;
  {
    this.interface := grp.interface;
    // add self to local_learners
    grp.local_learners := grp.local_learners[id := this];
  }

  method Learn(source_ID: int, round: int, value: int)
    requires this.interface != null && this.interface.valid();
  {
    this.interface.EventLearn(round, value);
  }

  predicate valid(grp: Group)
    requires grp != null;
    reads this, grp;
  {
    this.interface == grp.interface
  }
}


