include "Klon.dfy"
include "Context.dfy"
include "Xlone.dfy"
include "Bound.dfy"

//KJX_WARD_REFAC

method {:isolate_assertions} {:timeLimit 5} clone(a : Object, context : set<Object>,  into : Owner := a.owner)
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
    requires myBoundsOK(into, into)
    requires forall x <- context :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(context)

    requires myBoundsOK(into, into)
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


method {:isolate_assertions} {:timeLimit 20 } sheepKlon(o : Object, clowner : Owner, oHeap : set<Object>, clbound : Owner := froposeBounds(clowner)) returns  (m : Klon)
//seed Klon for cloning object o,  owner of clone being clowner, within heap oHeap...
   decreases *
    requires AllReady(clowner)
    requires AllReady(clbound)
    requires myBoundsOK(clowner, clbound)
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
    assert mep0.Keys == o.AMFX;
    reveal UniqueMapEntry();
    assert forall i <- mep0.Keys :: UniqueMapEntry(mep0, i);
    assert AllMapEntriesAreUnique(mep0);
    assert forall x <- mep0.Keys ::   x == mep0[x];

    var mep : vmap<Object,Object> := mep0;
//    assert mep.Keys == mep.Values == o.AMFX <= oHeap by  { reveal COK(); }
    assert mep.Keys == mep.Values == o.AMFX;
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
      }

reveal COK();
assert COK(o, oHeap);

var c := new Object.make(o.fieldModes, clowner, oHeap, "clone_of_" + o.nick, clbound);

assert c.Ready();
assert c.Valid();
assert c.Context(oHeap+{c});
assert c.fieldModes == o.fieldModes;


forall x <- oHeap ensures (x.Context(oHeap+{c}))
 { reveal COK();
   assert COK(x,oHeap);
   assert x.Ready();
   assert x.Valid();
   assert x.Context(oHeap);
   x.WiderContext(oHeap,oHeap+{c});
   assert x.Context(oHeap+{c});
 }

assert forall x <- mep.Keys ::  x == mep[x];  assert forall x <- mep.Keys ::  (x.fieldModes == mep[x].fieldModes);
var me := map2vmap(mep[o:=c]);
assert AllMapEntriesAreUnique(me);
assert forall x <- mep.Keys ::   x == me[x];  assert forall x <- mep.Keys ::  (x.fieldModes == me[x].fieldModes);
assert me[o] == c;                        assert forall x : Object <- {o} ::  (x.fieldModes == me[x].fieldModes);
assert me.Keys == mep.Keys + {o};   assert forall x : Object <- me.Keys ::  (x.fieldModes == me[x].fieldModes);

//
// assert forall x : Object <- me.Keys ::
//   (if (x == o)  then ((me[x] == c) && (x.fieldModes == me[x].fieldModes))
//                 else ((me[x] == x) && (x.fieldModes == me[x].fieldModes)))
//   && (x.fieldModes == me[x].fieldModes);

assert me.Keys == o.AMFO;
assert me.Values == o.AMFX+{c};
assert AllReady(me.Keys);
assert AllReady(me.Values);


// assert forall x <- me.Keys ::
//   (if (x == o)  then ((me[x] == c) && (c.Ready()))
//                 else ((me[x] == x) && (x.Ready())))
//    && me[x].Ready();
//
//
// assert forall x <- me.Keys ::
//   (if (x == o)  then ((me[x] == c) && (c.Context(oHeap+{c})))
//               else ((me[x] == x) && (x.Context(oHeap+{c})))
// ) && me[x].Context(oHeap+{c});

//NO_FIELDMODES
assert forall x <- me.Keys ::
(if (x == o)  then ((me[x] == c) && (c.fieldModes == o.fieldModes))
              else ((me[x] == x) && (me[x].fieldModes == x.fieldModes))
) && (me[x].fieldModes == x.fieldModes);

assert inside(o,o);
assert forall k <- me.Keys :: (not(inside(k,o)) ==> (me[k] == k));
forall x <- me.Values ensures (x.Context(me.Values+oHeap)) //by
  {
     assert x.Context(oHeap+{c});
     x.WiderContext(oHeap+{c},me.Values+oHeap);
     assert x.Context(oHeap+{c});
  }
assert forall x <- me.Values :: x.Context(me.Values+oHeap); ///Err

//
// assert forall k : Object <- me.Keys :: ( && (k.Ready()) && (objectInKlown(k)) && (me[k].Ready()) && (me[k] in hns()) );
//
// assert forall k <- me.Keys :: CalidLineKV(k, me[k]);
//
// assert forall x <- me.Values :: (x.AMFO <= hns());

assert forall k <- me.Keys :: ( (inside(k,o)) ==> (me[k] !in oHeap));

var clamfx := flatten(clowner);

assert AllReady(me.Keys);
assert AllReady(me.Values);

m := Klon(me,
                            o,
                            c,
                            clowner,
                            clbound,
                            oHeap,
                            o.AMFX,
                            clamfx,
                            flatten(clbound));

assert forall x <- m.m.Values :: x.Context(me.Values+oHeap);
assert m.hns() ==   me.Values+oHeap;
assert m.hns() ==  m.m.Values+m.oHeap;
assert forall x <- m.m.Values :: x.Context(m.hns());

assert o == m.o;
assert c == m.c == m.m[m.o];

    assert (m.o in m.oHeap);
    assert (m.o.Ready());
    assert (m.objectInKlown(m.o));
    assert (m.m[m.o] == m.c);
    assert (m.o.AMFX == m.o_amfx);
    assert (m.o.AMFO == m.o_amfx+{m.o});
    assert (m.clowner == m.c.owner);
    assert (m.clbound == m.c.bound);
    assert ((m.c.AMFX  == m.c_amfx));
    assert ((m.c.AMFB  == m.c_amfb));
    assert myBoundsOK(m.o.owner, m.o.bound);
    assert (m.oHeap >= m.c_amfx >= flatten(m.clbound) >= flatten(m.o.bound));
    assert (m.m.Keys <= m.oHeap);
    assert (m.m.Values <= m.hns());
    assert (forall x <- m.hns() :: x.Ready());
    assert (forall x <- m.m.Keys :: m.objectInKlown(x));
    assert (m.c_amfx <= m.oHeap);
    assert klonReady(m);

  assert m.o.Valid() && m.o.Context(m.oHeap);
  assert m.c.Valid() && m.c.Context(m.hns({m.c}));
  assert klonPivot(m);

  assert (forall x <- m.oHeap :: x.Context(m.oHeap));
  assert (forall x <- m.m.Values :: x.Context(m.hns()));
  assert klonHeap(m);

forall k <- m.m.Keys ensures klonLine(k, m.m[k], m) //by
 {
        var v := m.m[k];
        assert (k.Ready() && k in m.oHeap    && k.Valid());
        assert (v.Ready() && v in m.hns({v}) && v.Valid());
        assert (m.m.Keys >= k.AMFX);
        assert (k.AMFO >  k.AMFB);
        assert (v.AMFO >= v.AMFB);
        assert (v.AMFB >= k.AMFB);
    assert klonBound(k,v,m);

    assert klonModes(k,v,m);

        assert (m.o.Ready());
        assert (m.objectInKlown(m.o));
        assert ( (k == m.o)       <==>  (v == m.c)  );
        assert ((inside(k, m.o))   ==> (k.AMFB  <= m.o.AMFB));
        assert (outside(k, m.o)   <==>  (v == k));
        assert ( inside(k, m.o)   <==>  inside(v, m.c) );
        assert (outside(k, m.c));
        assert ((inside(k,m.o)) ==> (v !in m.oHeap));
    assert klonGeometry(k,v,m);

    assert klonIdentity(k,v,m);
 }

   assert klonAllLines(m);

//assert HighLineKV(o, c, m);

// assert m.m.Values == me.Values;
// assert forall x <-  me.Values :: x.Context(me.Values+oHeap);
// assert forall x <-  m.m.Values :: x.Context(m.hns());



// forall k <- m.m.Keys ensures (m.gettingThere()) {
//    if (k == c) {
//       assert (k.Ready()) && (m.objectInKlown(k)) && (m.m[k].Ready()) && (m.m[k] in m.hns());
//    } else {
//       assert (k.Ready()) && (m.objectInKlown(k)) && (m.m[k].Ready()) && (m.m[k] in m.hns());
//    }
//  assert (k.Ready()) && (m.objectInKlown(k)) && (m.m[k].Ready()) && (m.m[k] in m.hns());
// }



// Error: function precondition could not be proved
// Inside klonLine(k, m.m[k], m)
// Inside klonReady(m)
// Could not prove: m.m.Values <= m.hns()
// This is the only assertion in batch #775 of 1290 in method sheepKlon
// Batch #775 resource usage: 31.2M RU
//
// Error: possible violation of postcondition of forall statement
// Inside klonLine(k, m.m[k], m)
// Inside klonModes(k,v,m)
// Could not prove: k.fieldModes == v.fieldModes
// This is the only assertion in batch #644 of 1290 in method sheepKlon
// Batch #644 resource usage: 27.0M RU
//
// Error: function precondition could not be proved
// Inside klonLine(k, m.m[k], m)
// Inside klonReady(m)
// Could not prove: forall x <- m.m.Keys :: m.objectInKlown(x)
// This is the only assertion in batch #777 of 1290 in method sheepKlon
// Batch #777 resource usage: 25.8M RU

forall k <- m.m.Keys ensures (klonLine(k, m.m[k], m)) {
  if (k == c) {

   } else {

   }
  }

//
// assert m.AllLinesCalid();
// assert m.gettingThere();
// assert m.SuperCalidFragilistic();
// m := Xlone_All_Fields(o,c,m);
assert klonReady(m);
assert klonCalid(m);
assert m.c.Ready();
}












// //  forall x <- m.m.Keys ensures (true)  {
// // //    assert (outside(x,m.o)); //where the FUCK did this come from?
// //     assert (x.AMFX <= m.m.Keys);
// //     assert (x.AMFB <= m.m.Keys);
// //     assert (m.ownersInKlown(x));
// //     assert (x.Ready());
// //     assert (m.apoCalidse());
// //
// //   assert (x.owner <= m.m.Keys <= m.oHeap);
// //   assert (m.m.Values <= flatten( m.hns() ));
// //   assert (m.o.Ready());
// //   assert (m.HeapOwnersReady());
// //   assert (m.c_amfx <= m.oHeap);
// //   assert m.m[x].Ready();
// //     assert (checkOwnershipOfClone(x,m.m[x],m));
// //     assert (checkBoundOfClone(x,m.m[x],m));
// //     assert (mappingOwnersThruKlownKV(x,m.m[x],m));
// //  }
//
//
// forall k <- m.m.Keys ensures (true) {
//      assert (k.Ready());
//      assert (m.objectInKlown(k));
//      assert (m.m[k].Ready());
//      assert (m.m[k] in m.hns());
// }
//
// forall k <- m.m.Keys ensures (HighLineKV(k, m.m[k], m)) {
//   if (k == o) {
//     assert m.m[k] == c;
//     assert HighLineKV(o, c, m);
//   } else {
//     assert m.m[k] == k;
//     assert HighLineKV(k, m.m[k], m);
//   }
// }
//
//   assert m.AllLinesCalid();
//   assert m.gettingThere();
//   assert m.SuperCalidFragilistic();
//
//  m := Xlone_All_Fields(o,c,m);
//
//
// // assert forall x <- m.m.Keys :: (
// //     && (outside(x,m.o))
// //     && (x.AMFX <= m.m.Keys)
// //     && (x.AMFB <= m.m.Keys)
// // //    && (k.bound <= k.owner <= m.Keys)
// //     && (m.ownersInKlown(x))  //belt and braces--- currently a requirement!
// //
// //   && (x.Ready())
// //   && (m.ownersInKlown(x))
// //   && (x.Ready())
// //   && (m.apoCalidse())
// //   && (x.owner <= m.m.Keys <= m.oHeap)
// //   && (m.m.Values <= flatten( m.hns() ))
// //   && (m.o.Ready())
// //   && (m.HeapOwnersReady())
// //   && (m.c_amfx <= m.oHeap)
// //
// //     && (checkOwnershipOfClone(x,x,m))
// //     && (checkBoundOfClone(x,x,m))
// //     && (mappingOwnersThruKlownKV(x,x,m))
// // );
//
//
// assert m.SuperCalidFragilistic();
//
// forall x <- m.m.Keys ensures (m.CalidLineKV(x,m.m[x])) //GRRR (m.CalidLineKV(x,m.m[x])) //by
// {
//    // assert (outside(x,m.o));
//     assert (x.AMFX <= m.m.Keys);  //???
//     assert (x.AMFB <= m.m.Keys); //???
//       assert (m.ownersInKlown(x)) ; //???
//     assert (x.Ready()); //??? //??? //??? //??? //??? //???
//     assert (m.ownersInKlown(x));
//     assert (x.Ready());
// //    assert (m.apoCalidse());
//     assert (x.owner <= m.m.Keys <= m.oHeap);  //???
//     assert (m.m.Values <= flatten( m.hns() ));
//     assert (m.o.Ready()); //???
//     assert (m.HeapOwnersReady()); //???
//     assert (m.c_amfx <= m.oHeap);            //???
//     assert (checkOwnershipOfClone(x,m.m[x],m));        //???        //???
//     assert (checkBoundOfClone(x,m.m[x],m));
//     assert (mappingOwnersThruKlownKV(x,m.m[x],m)); //???
// }
//
// // // assert forall x <- m.m.Keys :: m.CalidLineKV(x,x);
// //
// //
// //   // assert m.hns() == oHeap + clamfx;
// //     assert m.oHeap == oHeap;
// //
// //     assert o.AMFX == m.o_amfx <= m.m.Keys;
// //
// //     assert COK(o, oHeap);   reveal COK();
// //     assert COK(o, m.oHeap);
// //
// //     assert m.oHeap == oHeap;
// //
// //     assert CallOK(oHeap);
// //     assert forall x <- oHeap :: x.Ready();
// //
// //     assert m.o.Ready();
// //     assert (m.o.AMFX <= m.m.Keys);
// //
// //
// //     assert (m.m.Keys <= m.oHeap);
// //     assert (m.m.Values <= m.hns());
// //     assert (m.ownersReadyInKlown(o));
// //     assert (m.HeapOwnersReady());
// //     assert (m.c_amfx <= m.oHeap);
