include "Klon.dfy"
include "Context.dfy"
include "Xlone.dfy"
include "Bound.dfy"

//KJX_WARD_REFAC

lemma PLUS_EMPTY(a : Owner, b : Owner)
  ensures a + b == (a + b) + {} == a + b + {}
{}

method {:timeLimit 5} clone(a : Object, context : set<Object>,  into : Owner := a.owner)
     returns (b : Object, subtext : set<Object>)
   decreases *
    requires COK(a, context)
    requires AllReady(into)
    requires flatten(into) >= a.AMFB
    requires flatten(proposeBounds(into)) >= a.AMFB
    requires CallOK(context)
    requires context >= flatten(into)   //GRR
    requires flatten(into) >= a.AMFB
    requires flatten(into) >= a.AMFB
    requires forall o <- flatten(into) :: o.Ready()
    requires boundsOK(into, into)
    requires forall x <- context :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(context)

    requires boundsOK(into, into)
    requires COK(a, context)
    requires CallOK(context)
    requires forall x <- context :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(context)

     requires context >= a.AMFB
     requires context >= flatten(into)
     requires flatten(into) >= flatten(into)
     requires flatten(into) >= a.AMFB

    requires context >= flatten(into) >= flatten(into) >= a.AMFB
    requires forall o <- flatten(into) :: o.Ready()

//NOCONTEX
    requires context >= a.AMFO
    requires a.Ready()




     ensures b.Valid()
{
  reveal COK();
  var fp := proposeBounds(into);
  FroposeGetsBoundsOK(into,fp);
  assert flatten(into) >= flatten(proposeBounds(into));
  var  rm := sheepKlon(a, into, context, proposeBounds(into));

  assert klonReady(rm);
  assert klonCalid(rm);

  subtext := rm.hns();
  b := rm.c;
}


method {:timeLimit 30 } sheepKlon(o : Object, clowner : Owner, oHeap : set<Object>, clbound : Owner := froposeBounds(clowner)) returns  (m : Klon)
//seed Klon for cloning object o,  owner of clone being clowner, within heap oHeap...
   decreases *
    requires AllReady(clowner)
    requires AllReady(clbound)
    requires boundsOK(clowner, clbound)
    requires COK(o, oHeap)
    requires CallOK(oHeap)
    requires forall x <- oHeap :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(oHeap)

     requires oHeap >= o.AMFB
     requires oHeap >= flatten(clowner)
     requires flatten(clowner) >= flatten(clbound)
     requires flatten(clbound) >= o.AMFB

    requires oHeap >= flatten(clowner) >= flatten(clbound) >= o.AMFB
    requires forall o <- flatten(clowner) :: o.Ready()

//NOCONTEX
    requires oHeap >= o.AMFO
    requires o.Ready()
//NOCONTEXT all below
    // ensures (m.m.Keys <= m.oHeap)
    // ensures (m.m.Values <= m.hns())
    // ensures (m.HeapOwnersReady())
    // ensures (m.c_amfx <= m.oHeap)
    // ensures forall x <- oHeap :: (x.Ready() && x.Valid() && x.Context(oHeap))

   ensures COK(o, m.oHeap)
//KJX_WARD_REFAC    ensures m.SuperCalidFragilistic()
   ensures klonReady(m)
   ensures klonCalid(m)
   ensures m.c.Ready()
    {
     assert CallOK(oHeap); reveal CallOK(); reveal COK();
     assert forall x <- oHeap :: (reveal COK(); COK(x,oHeap));
     assert forall x <- oHeap :: (reveal COK(); COK(x,oHeap) && x.Ready() && x.Valid() && x.Context(oHeap));
     assert forall x <- oHeap :: (x.Ready() && x.Valid() && x.Context(oHeap));

    var mep0 := map x <- o.AMFX :: x;
    assert mep0.Keys == o.AMFX; assert o !in mep0.Keys;
    reveal UniqueMapEntry();
    assert forall i <- mep0.Keys :: UniqueMapEntry(mep0, i);
    assert AllMapEntriesAreUnique(mep0);
    assert forall x <- mep0.Keys ::   x == mep0[x];

    var mep : vmap<Object,Object> := mep0;
//    assert mep.Keys == mep.Values == o.AMFX <= oHeap by  { reveal COK(); }
    assert mep.Keys == mep.Values == o.AMFX;  assert o !in mep.Keys;
    assert forall x <- mep.Keys ::   x == mep[x];

    forall x <- mep.Keys ensures true //by
      {
        assert x.Ready();
        assert x.Valid();
        assert outside(x,o);
        assert (inside(x,o)) ==> (mep[x] !in oHeap);
        assert x in oHeap;
        assert x == mep[x];
        assert mep[x].Ready();
        assert x.Context(oHeap);
        assert x.Context(oHeap+mep.Values);
        assert x.AMFO <= mep.Keys;

        assert mep[x].AMFB >= x.AMFB; //OK cos mep[x] == x
      }
assert forall x <- mep.Keys :: mep[x].AMFB >= x.AMFB;
reveal COK();
assert COK(o, oHeap);

var c := new Object.make(o.fieldModes, clowner, oHeap, "clone_of_" + o.nick, clbound);

assert c.Ready();
assert c.Valid();
assert c.Context(oHeap+{c});
assert c.fieldModes == o.fieldModes;
assert c.AMFB >= o.AMFB;

forall x <- oHeap ensures (x.Context(oHeap+{c}))
 { reveal COK();
   assert COK(x,oHeap);
   assert x.Ready();
   assert x.Valid();
   assert x.Context(oHeap);
   x.WiderContext(oHeap,oHeap+{c});
   assert x.Context(oHeap+{c});
 }

assert forall x <- mep.Keys ::  x == mep[x];  //19Sep assert forall x <- mep.Keys ::  (x.fieldModes == mep[x].fieldModes);
var me := map2vmap(mep[o:=c]);  //19Sep assert me.Keys == mep.Keys + {o}; assert me.Values == mep.Values + {c};
assert AllMapEntriesAreUnique(me);
assert forall x <- mep.Keys ::   x == me[x]; //19Sep  assert forall x <- mep.Keys ::  (x.fieldModes == me[x].fieldModes);
assert me[o] == c;                       //19Sep assert forall x : Object <- {o} ::  (x.fieldModes == me[x].fieldModes);
assert me.Keys == mep.Keys + {o};  //19Sep  assert forall x : Object <- me.Keys ::  (x.fieldModes == me[x].fieldModes);
assert me.Values == mep.Values + {c};
//
// assert forall x : Object <- me.Keys ::
//   (if (x == o)  then ((me[x] == c) && (x.fieldModes == me[x].fieldModes))
//                 else ((me[x] == x) && (x.fieldModes == me[x].fieldModes)))
//   && (x.fieldModes == me[x].fieldModes);

assert me.Keys == o.AMFX+{o};
assert me.Values == o.AMFX+{c};
assert AllReady(me.Keys); assert AllReady(me.Values);
assert AllValid(me.Keys); assert AllValid(me.Values);

assert forall x <- mep.Keys :: x == mep[x] == me[x];
assert forall x <- mep.Keys :: x.AMFB == mep[x].AMFB == me[x].AMFB;
assert c.AMFB >= o.AMFB;

assert (me[o] == c) && (c.AMFB >= o.AMFB)   && (me[o].AMFB >= c.AMFB);

assert forall x <- me.Keys ::
  &&  (if (x == o) then ((me[o] == c) && (c.AMFB >= o.AMFB)      && (me[o].AMFB >= x.AMFB))
                   else ((me[x] == x) && (mep[x].AMFB >= x.AMFB) && (me[x].AMFB >= x.AMFB)));

 assert forall x <- me.Keys :: (me[x].AMFB >= x.AMFB);


//NO_FIELDMODES
assert (o.fieldModes == c.fieldModes) && (me[o] == c) && (o.fieldModes == me[o].fieldModes);
// assert forall x <- me.Keys ::
// (if (x == o)  then ((me[o] == c) && (o.fieldModes == c.fieldModes))
//               else ((me[x] == x) && (me[x].fieldModes == x.fieldModes))
// ) && (me[x].fieldModes == x.fieldModes);


forall x <- me.Keys ensures (me[x].fieldModes == x.fieldModes) //by
 {
   if (x == o)  {
                assert (me[o] == c);
                assert (o.fieldModes == c.fieldModes);
                assert me[x].fieldModes == x.fieldModes;
               } else {
                assert (me[x] == x);
                assert me[x].fieldModes == x.fieldModes;
               }
 }


assert inside(o,o);
assert forall k <- me.Keys :: (not(inside(k,o)) ==> (me[k] == k));
forall x <- me.Values ensures (x.Context(me.Values+oHeap)) //by
  {
     assert x.Context(oHeap+{c});
     x.WiderContext(oHeap+{c},me.Values+oHeap);
     assert x.Context(me.Values+oHeap);
  }
assert forall x <- me.Values :: x.Context(me.Values+oHeap); ///Err
assert ME_VALUES: forall x <- me.Values :: x.Context(me.Values+oHeap); ///Err
//
// assert forall k : Object <- me.Keys :: ( && (k.Ready()) && (objectInKlon(k)) && (me[k].Ready()) && (me[k] in hns()) );
//
// assert forall k <- me.Keys :: CalidLineKV(k, me[k]);
//
// assert forall x <- me.Values :: (x.AMFO <= hns());

assert forall k <- me.Keys :: ( (inside(k,o)) ==> (me[k] !in oHeap));

var clamfx := flatten(clowner);

assert AllReady(me.Keys);
assert AllReady(me.Values);
assert forall x <- me.Keys :: me[x].AMFB >= x.AMFB;
m := Klon(me,
                            o,
                            c,
                            clowner,
                            clbound,
                            oHeap,
                            o.AMFX,
                            clamfx,
                            flatten(clbound));

//19Sep assert m.m == me;  assert m.oHeap == oHeap;
// assert forall x <- me.Values :: x.Context(me.Values+oHeap) by { reveal ME_VALUES; }
// assert forall x <- m.m.Values :: x.Context(m.m.Values+oHeap);
// assert (m.m.Values+oHeap)+{} == (m.m.Values+oHeap) by { PLUS_EMPTY(m.m.Values, oHeap); }
// assert forall x <- m.m.Values :: x.Context((m.m.Values+oHeap)+{});
// assert m.hns() == (m.m.Values+oHeap)+{} == (m.m.Values+oHeap) by { PLUS_EMPTY(m.m.Values, oHeap); }
// assert forall x <- m.m.Values :: x.Context(m.hns());

assert forall x <- m.m.Keys :: (m.m[x] == me[x]) && (m.m[x].AMFB >= x.AMFB);

assert o == m.o;
assert c == m.c == m.m[m.o];

    assert (m.o in m.oHeap);
    assert (m.o.Ready());
    assert (m.objectInKlon(m.o));
    assert (m.m[m.o] == m.c);
    assert (m.o.AMFX == m.o_amfx);
    assert (m.o.AMFO == m.o_amfx+{m.o});
    assert (m.clowner == m.c.owner);
    assert (m.clbound == m.c.bound);
    assert ((m.c.AMFX  == m.c_amfx));
    assert ((m.c.AMFB  == m.c_amfb));
    assert boundsOK(m.o.owner, m.o.bound);
    assert (m.oHeap >= m.c_amfx >= flatten(m.clbound) >= flatten(m.o.bound));
    assert (m.m.Keys <= m.oHeap);
    assert (m.m.Values <= m.hns());
    assert (forall x <- m.hns() :: x.Ready());
    assert (forall x <- m.m.Keys :: m.objectInKlon(x));
    assert (m.c_amfx <= m.oHeap);
    assert klonReady(m);

  assert m.o.Valid() && m.o.Context(m.oHeap);
  assert m.c.Valid() && m.c.Context(m.hns({m.c}));
  assert klonPivot(m);

  assert (forall x <- m.oHeap :: x.Context(m.oHeap));
  assert (forall x <- m.m.Values :: x.Context(m.hns()));
  assert klonHeap(m); klonHeapValid(m);
  assert forall  x <- m.m.Keys :: x.Valid() && m.m[x].Valid();
forall k <- m.m.Keys ensures klonLine(k, m.m[k], m) //by
 {
        var v := m.m[k]; assert v in m.m.Values; assert v.Context(m.hns());
        assert (k.Ready() && k in m.oHeap    && k.Valid()) && k.Context(m.oHeap);
        assert (v.Ready() && v in m.hns({v}) && v.Valid()) && v.Context(m.hns({v}));
        assert (m.m.Keys >= k.AMFX);
        assert (k.AMFO >  k.AMFB);
        assert (v.AMFO >= v.AMFB);
        assert (v.AMFB >= k.AMFB);
    assert klonBound(k,v,m);

    assert klonModes(k,v,m);

        assert (m.o.Ready());
        assert (m.objectInKlon(m.o));
        assert ( (k == m.o)       <==>  (v == m.c)  );
        assert ((inside(k, m.o))   ==> (k.AMFB  <= m.o.AMFB));
        assert (outside(k, m.o)   <==>  (v == k));
        assert ( inside(k, m.o)   <==>  inside(v, m.c) );
        assert (outside(k, m.c));
        assert ((inside(k,m.o)) ==> (v !in m.oHeap));
    assert klonGeometry(k,v,m);

    assert klonIdentity(k,v,m);
 }
//this is not a drill...
   assert klonAllLines(m);

//assert HighLineKV(o, c, m);

// assert m.m.Values == me.Values;
// assert forall x <-  me.Values :: x.Context(me.Values+oHeap);
// assert forall x <-  m.m.Values :: x.Context(m.hns());



// forall k <- m.m.Keys ensures (m.gettingThere()) {
//    if (k == c) {
//       assert (k.Ready()) && (m.objectInKlon(k)) && (m.m[k].Ready()) && (m.m[k] in m.hns());
//    } else {
//       assert (k.Ready()) && (m.objectInKlon(k)) && (m.m[k].Ready()) && (m.m[k] in m.hns());
//    }
//  assert (k.Ready()) && (m.objectInKlon(k)) && (m.m[k].Ready()) && (m.m[k] in m.hns());
// }



forall k <- m.m.Keys ensures (klonLine(k, m.m[k], m)) {
  if (k == c) {

   } else {

   }
  }


assert klonReady(m);
assert klonCalid(m);
assert m.c.Ready();
}
