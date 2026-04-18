  include "Klon.dfy"
include "Context.dfy"
include "Xlone.dfy"
include "Bound.dfy"

method {:isolate_assertions} {:timeLimit 10} clone(a : Object, context : set<Object>,  into : Owner := a.owner)
     returns (b : Object, subtext : set<Object>)
   decreases *
    requires COK(a, context)
    requires flatten(into) >= a.AMFB
    requires CallOK(context)
    requires context >= flatten(into) >= flatten(into)   //GRR
    requires flatten(into) >= flatten(into)
    requires forall o <- flatten(into) :: o.Ready()
    requires myBoundsOK(into, into)
    requires forall x <- context :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(context)

     ensures b.Valid()
{
  reveal COK();
  assert flatten(proposeBounds(into)) >= into;
  var  rm := sheepKlon(a, into, context, proposeBounds(into));

  assert rm.SuperCalidFragilistic();

  subtext := rm.hns();
  b := rm.o;
}


method {:isolate_assertions} {:timeLimit 30 } sheepKlon(o : Object, clowner : Owner, oHeap : set<Object>, clbound : Owner := froposeBounds(clowner)) returns  (m : Klon)
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
   ensures m.SuperCalidFragilistic()

//    reads oHeap`fields, oHeap`fieldModes
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

    var mep : vmap<Object,Object> := mep0;
//    assert mep.Keys == mep.Values == o.AMFX <= oHeap by  { reveal COK(); }
    assert mep.Keys == mep.Values == o.AMFX;

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

        //assert mep0.Keys >= o.AMFX >= o.AMFB;
        //assert mep0.Keys >= mep0[o].AMFX >= mep0[o].AMFB;
      }
    // var mTKoA := mapThruVMap(o.AMFX, mep);
    // var oxtra := mTKoA - clamfx;
    // var cxtra := clamfx - mTKoA;


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

assert AllReady(mep.Keys);
assert AllReady(mep.Values);

//put o := into the map
var me := map2vmap(mep[o:=c]);
assert AllMapEntriesAreUnique(me);



assert forall x <- me.Keys ::
(if (x == o)  then ((me[x] == c) && (c.Ready()))
              else ((me[x] == x) && (x.Ready()))
) && me[x].Ready();


assert forall x <- me.Keys ::
(if (x == o)  then ((me[x] == c) && (c.Context(oHeap+{c})))
              else ((me[x] == x) && (x.Context(oHeap+{c})))
) && me[x].Context(oHeap+{c});

//NO_FIELDMODES
// assert forall x <- me.Keys ::
// (if (x == o)  then ((me[x] == c) && (c.fieldModes == o.fieldModes))
//               else ((me[x] == x) && (me[x].fieldModes == x.fieldModes))
// ) && (me[x].fieldModes == x.fieldModes);

assert inside(o,o);
assert forall k <- me.Keys :: (not(inside(k,o)) ==> (me[k] == k));
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

var m0 : Klon := Klon(me,
                            o,
                            c,
                            clowner,
                            clbound,
                            oHeap,
                            o.AMFX,
                            clamfx,
                            flatten(clbound));

assert o == m0.o;
assert c == m0.c == m0.m[m0.o];
// assert inside(o, o);
// assert inside(c, c);
// assert inside(m0.o, m0.o);
// assert inside(m0.m[m0.o], m0.m[m0.o]);
// assert outside(m0.o, m0.o) <==> (m0.o == m0.m[m0.o]);
// assert inside(m0.o, m0.o) <==> inside(m0.m[m0.o], m0.m[m0.o]);
// assert inside(m0.m[m0.o], m0.m[m0.o]);

//assert HighLineKV(o, c, m0);

// assert m0.m.Values == me.Values;
// assert forall x <-  me.Values :: x.Context(me.Values+oHeap);
// assert forall x <-  m0.m.Values :: x.Context(m0.hns());

forall k <- m0.m.Keys ensures (m0.gettingThere()) {
   if (k == c) {
      assert (k.Ready()) && (m0.objectInKlown(k)) && (m0.m[k].Ready()) && (m0.m[k] in m0.hns());
   } else {
      assert (k.Ready()) && (m0.objectInKlown(k)) && (m0.m[k].Ready()) && (m0.m[k] in m0.hns());
   }
 assert (k.Ready()) && (m0.objectInKlown(k)) && (m0.m[k].Ready()) && (m0.m[k] in m0.hns());
}



forall k <- m0.m.Keys ensures (m0.CalidLineKV(k, m0.m[k])) {
  if (k == c) {

   } else {

   }
  }

//
// assert m0.AllLinesCalid();
// assert m0.gettingThere();
// assert m0.SuperCalidFragilistic();
m := m0;
// m := Xlone_All_Fields(o,c,m0);
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
// forall k <- m0.m.Keys ensures (true) {
//      assert (k.Ready());
//      assert (m0.objectInKlown(k));
//      assert (m0.m[k].Ready());
//      assert (m0.m[k] in m0.hns());
// }
//
// forall k <- m0.m.Keys ensures (HighLineKV(k, m0.m[k], m0)) {
//   if (k == o) {
//     assert m0.m[k] == c;
//     assert HighLineKV(o, c, m0);
//   } else {
//     assert m0.m[k] == k;
//     assert HighLineKV(k, m0.m[k], m0);
//   }
// }
//
//   assert m0.AllLinesCalid();
//   assert m0.gettingThere();
//   assert m0.SuperCalidFragilistic();
//
//  m := Xlone_All_Fields(o,c,m0);
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
