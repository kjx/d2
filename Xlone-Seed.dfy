include "Klon.dfy"
include "Context.dfy"
include "Xlone.dfy"
include "Bound.dfy"

method {:isolate_assertions} clone(a : Object, context : set<Object>,  into : Owner := a.owner)
    returns (b : Object, subtext : set<Object>)
decreases *
  requires COK(a, context)
  requires flatten(into) >= a.AMFB
  requires CallOK(context)
    requires context >= flatten(into) >= flatten(into)   //GRR
    requires flatten(into) >= flatten(into)
    requires forall o <- flatten(into) :: o.Ready()
    requires myBoundsOK(into, into)  //hmm
  requires forall x <- context :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(context)
{
  var m0 : Klon := seed(a, into, context);

  assert m0.StupidCalidFragilistic();

  var m1 : Klon;

  reveal COK();

  assert COK(a, m0.oHeap);
  assert klonCanKV(m0,a,a);


  b := new Object.make(a.fieldModes, m0.clowner, m0.oHeap, "clone_of_" + a.nick, m0.clbound);

    assert m0.StupidCalidFragilistic();
    assert a.Ready();
    assert m0.ownersInKlown(a);
    assert m0.o.Ready();
    assert m0.objectInKlown(m0.o);
    assert m0.CalidCanKey(a);
    assert a !in m0.m.Keys;
    assert b !in m0.m.Values;
    assert a in m0.oHeap;
    assert b.Ready() ;
    assert b.Valid() ;
    assert b.Context(m0.hns({b}));
    assert m0.m.Keys <= m0.oHeap;
    assert klonVMapOK(m0.m);
    assert klonCanKV(m0,a,b);
    assert m0.CalidLineKV(a,b);

  assert m0.CKV_preconditions(a,b);
  assert m0.CalidLineKV(a,b);

  assert m0.StupidCalidFragilistic();
  assert m0.ownersInKlown(m0.o);

  m1 := m0.CalidKV(a,b);
  assert a == m0.o == m1.o;
  assert m1.o in m1.m.Keys;
  assert m1.objectInKlown(m1.o);
  assert m1.SuperCalidFragilistic();
  var rm := Xlone_All_Fields(a,b,m1);
  assert rm.SuperCalidFragilistic();
  subtext := rm.hns();
}

lemma {:isolate_assertions} STOOPID(x : Object, oHeap : set<Object>)
   requires COK(x,oHeap)
    ensures reveal COK(x); COK(x,oHeap) && x.Ready() && x.Valid() && x.Context(oHeap)
  {
  assert COK(x,oHeap);
  reveal COK();
  assert x.Ready() && x.Valid() && x.Context(oHeap);
  }

lemma {:isolate_assertions} STOOPID_TOO(m : Klon)
   requires m.StupidCalidFragilistic()
   requires m.objectInKlown(m.o)
    ensures m.SuperCalidFragilistic()
{}

function {:isolate_assertions} {:timeLimit 15}  seed(o : Object, clowner : Owner, oHeap : set<Object>) : (m : Klon)
//seed Klon for cloning object o,  owner of clone being clowner, within heap oHeap...
    requires COK(o, oHeap)
    requires CallOK(oHeap)
    requires forall x <- oHeap :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(oHeap)

    requires oHeap >= flatten(clowner) >= flatten(clowner)   //GRR
    requires flatten(clowner) >= flatten(clowner)
    requires forall o <- flatten(clowner) :: o.Ready()
    requires myBoundsOK(clowner, clowner)
    requires myBoundsOK(o.owner, o.bound)  //GRR update ready?

    ensures (m.m.Keys <= m.oHeap)
    ensures (m.m.Values <= m.hns())
    ensures (m.ownersReadyInKlown(o))  //not obejctReadyInCloneapparentlyt...  FUCK need to look at Xlone-MAIN I BET
    ensures (m.HeapOwnersReady())
    ensures (m.c_amfx <= m.oHeap)
    ensures forall x <- oHeap :: (x.Ready() && x.Valid() && x.Context(oHeap))

    ensures m.StupidCalidFragilistic() /// cos obkject aint in the KLON at this ponmt..
    ensures COK(o, m.oHeap)
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
     assert CallOK(oHeap); reveal CallOK(); reveal COK();
     assert forall x <- oHeap :: (reveal COK(); COK(x,oHeap));
     assert forall x <- oHeap :: (reveal COK(); COK(x,oHeap) && x.Ready() && x.Valid() && x.Context(oHeap));
     assert forall x <- oHeap :: (x.Ready() && x.Valid() && x.Context(oHeap));

    var mep0 := map x <- o.AMFX :: x;

    var clamfx := flatten(clowner);

    reveal UniqueMapEntry();
    assert forall i <- mep0.Keys :: UniqueMapEntry(mep0, i);
    assert AllMapEntriesAreUnique(mep0);

    var mep : vmap<Object,Object> := mep0;

    assert mep.Keys == mep.Values == o.AMFX <= oHeap by  { reveal COK(); }

    forall x <- mep.Keys ensures true //by
      {
        assert x.Ready();
        assert outside(x,o);
        assert (inside(x,o)) ==> (mep[x] !in oHeap);
        assert x in oHeap;

        //assert mep0.Keys >= o.AMFX >= o.AMFB;
        //assert mep0.Keys >= mep0[o].AMFX >= mep0[o].AMFB;
      }
    var mTKoA := mapThruVMap(o.AMFX, mep);
    var oxtra := mTKoA - clamfx;
    var cxtra := clamfx - mTKoA;



    var m : Klon := Klon(mep,
                            o,
//                          o.AMFX,
                            clowner,
                            proposeBounds(clowner),
                            // clamfx,
                            // oxtra,
                            // cxtra,
                            oHeap,
                            o.AMFX,
                            clamfx);

// assert forall x <- m.m.Keys :: (
//     && (outside(x,m.o))
//     && (x.AMFX <= m.m.Keys)
//     && (x.AMFB <= m.m.Keys)
// //    && (k.bound <= k.owner <= m.Keys)
//     && (m.ownersInKlown(x))  //belt and braces--- currently a requirement!
//
//   && (x.Ready())
//   && (m.ownersInKlown(x))
//   && (x.Ready())
//   && (m.apoCalidse())
//   && (x.owner <= m.m.Keys <= m.oHeap)
//   && (m.m.Values <= flatten( m.hns() ))
//   && (m.o.Ready())
//   && (m.HeapOwnersReady())
//   && (m.c_amfx <= m.oHeap)
//
//     && (checkOwnershipOfClone(x,x,m))
//     && (checkBoundOfClone(x,x,m))
//     && (mappingOwnersThruKlownKV(x,x,m))
// );


forall x <- m.m.Keys ensures (true) //GRRR (m.CalidLineKV(x,x)) //by
{
    assert (outside(x,m.o));
    assert (x.AMFX <= m.m.Keys);
    assert (x.AMFB <= m.m.Keys);
    assert (m.ownersInKlown(x)) ;
    assert (x.Ready());
    assert (m.ownersInKlown(x));
    assert (x.Ready());
//    assert (m.apoCalidse());
    assert (x.owner <= m.m.Keys <= m.oHeap);
    assert (m.m.Values <= flatten( m.hns() ));
    assert (m.o.Ready());
    assert (m.HeapOwnersReady());
    assert (m.c_amfx <= m.oHeap);
    assert (checkOwnershipOfClone(x,x,m));
    assert (checkBoundOfClone(x,x,m));
    assert (mappingOwnersThruKlownKV(x,x,m));
}

// assert forall x <- m.m.Keys :: m.CalidLineKV(x,x);


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


    assert (m.m.Keys <= m.oHeap);
    assert (m.m.Values <= m.hns());
    assert (m.ownersReadyInKlown(o));
    assert (m.HeapOwnersReady());
    assert (m.c_amfx <= m.oHeap);

    m
    }
