include "Klon.dfy"
include "Context.dfy"
include "Xlone.dfy"

method {:isolate_assertions} clone(a : Object, context : set<Object>,  into : Owner := a.owner)
    returns (b : Object, subtext : set<Object>)
decreases *
  requires COK(a, context)
  requires flatten(into) >= a.AMFB
  requires CallOK(context)
  requires forall x <- context :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(context)
{
  var m0 : Klon := seed(a, into, context);
  var m1 : Klon;

  assume m0.SuperCalidFragilistic();  ///HMMMM.
  assert COK(a, m0.oHeap);
  assert klonCanKV(m0,a,a);

  b, m1 := Xlone_Via_Map(a, m0);

  subtext := m1.hns();
}

//   var m' : Klon := Klon(map[],    //m clonemap
//                a,       // o - object to be cloned / pivot / top object
//                a.AMFO,  // o_amfo AMFO of o
//                into,    // c_owner - proposewd owner of clone
//                flatten(into),   // c_amfx - AMFX of clone
//                {},
//                {},
//                context,      // oHeap
//                {}            // ns );
//               );
//
//   assert a in context;
//   assert m'.m.Keys == {} == m'.m.Values;
//
//   assert m'.calid() by {
//
//     reveal m'.calidObjects(); assert m'.calidObjects();
//     reveal m'.calidOK();
//
//     assert (m'.o in m'.oHeap);
//     assert (m'.m.Keys <= m'.oHeap);
//     assert (m'.m.Values <= m'.oHeap+m'.ns);
//     assert COK(m'.o, m'.oHeap);
//     assert CallOK(m'.oHeap);
//
//     reveal CallOK();
//     assert CallOK(m'.m.Keys, m'.oHeap) by { assert m'.m.Keys == {}; }
//     assert CallOK(m'.m.Values, m'.oHeap+m'.ns) by { assert m'.m.Values == {}; }
//     assert CallOK(m'.ns, m'.oHeap+m'.ns) by { assert m'.ns == {}; }
//
//     assert forall x <- m'.oHeap :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(m'.oHeap);
//
//
//     assert m'.calidOK();
//     reveal m'.calidMap();     assert m'.calidMap();
//     reveal m'.calidSheep();   assert m'.calidSheep();
//
//     reveal m'.calid();        assert m'.calid();
//   }
//
//
//   assert allMapOwnersThruKlownOK(m');
//
//   assert klonCanKV(m',a,a);
//
// //  assert m'.readyAll() by { assert m'.m.Keys == {}; }
//
//   assert forall o <- m'.m.Keys :: mappingOwnersThruKlownOK(o,m');
//
//   assert allMapOwnersThruKlownOK(m');
//
//   assert klonCanKV(m',a,a);  //hmm, interesting... technically not right but;
//         //not, this IS ruight...



function {:isolate_assertions} {:timeLimit 30}  seed(o : Object, clowner : Owner, oHeap : set<Object>) : (m : Klon)
//seed Klon for cloning object o,  owner of clone being clowner, within heap oHeap...
    requires COK(o, oHeap)
    requires CallOK(oHeap)
    requires forall x <- oHeap :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(oHeap)
//    ensures m.apoCalidse()

    ensures (m.m.Keys <= m.oHeap)
    ensures (m.m.Values <= m.hns())
    ensures (m.ownersReadyInKlown(o))  //not obejctReadyInCloneapparentlyt...  FUCK need to look at Xlone-MAIN I BET
    ensures (m.HeapOwnersReady())
    ensures (m.c_amfx <= m.oHeap)

//    ensures m.ownersInKlow n(o)
//    ensures m.SuperCalidFragilistic()
//    ensures COK(o, m.oHeap)


//    ensures allMapOwnersThruKlownIfInsideOK(m)
//
//     ensures m == Klon( (map x <- o.AMFX :: x),
//         o,
//         o.AMFX,
//         clowner,
//         flatten(clowner),
//         (flatten(clowner) - mapThruKlon(o.AMFX, m)),
//         (mapThruKlon(o.AMFX, m) - flatten(clowner)),
//         oHeap,
//         {} )


    reads oHeap`fields, oHeap`fieldModes
    {

    var mep0 := map x <- o.AMFX :: x;

    var clamfx := flatten(clowner);

    reveal UniqueMapEntry();
    assert forall i <- mep0.Keys :: UniqueMapEntry(mep0, i);
    assert AllMapEntriesAreUnique(mep0);

    var mep : vmap<Object,Object> := mep0;

    assert mep.Keys == mep.Values == o.AMFX <= oHeap by  { reveal COK(); }

    forall x <- mep0.Keys ensures true //by
      {
        assert x.Ready();
        //assert mep0.Keys >= o.AMFX >= o.AMFB;
        //assert mep0.Keys >= mep0[o].AMFX >= mep0[o].AMFB;
      }
    var mTKoA := mapThruVMap(o.AMFX, mep);
    var oxtra := mTKoA - clamfx;
    var cxtra := clamfx - mTKoA;



    var m : Klon :=
                       Klon(mep,
                            o,
//                          o.AMFX,
                            clowner,
                            clowner,
                            // clamfx,
                            // oxtra,
                            // cxtra,
                            oHeap,
                            o.AMFX,
                            clamfx);

  // assert m.hns() == oHeap + clamfx;
    assert m.oHeap == oHeap;

    assert o.AMFX == m.o_amfx <= m.m.Keys;

    assert COK(o, oHeap);   reveal COK();
    assert COK(o, m.oHeap);

    assert m.oHeap == oHeap;

    assert CallOK(oHeap);
    assert forall x <- oHeap :: x.Ready();

assert m.o.Ready();
assert (m.o.AMFX <= m.m.Keys);


//     assert (m.m.Keys <= m.oHeap);
//     assert (m.m.Values <= m.hns());
//    assert (m.objectReadyInKlown(o));
//     assert (m.HeapOwnersReady());
//     assert (m.c_amfx <= m.oHeap);

    m
    }
