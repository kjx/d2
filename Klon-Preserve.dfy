//include "Ownership.dfy"
include "Ownership-Split.dfy"


//this all depends on Klon, soi shohjld be renamed into Klon
// the stuff that depenmds on the Klon are doing the "vertical" mapping
// between original and clojne

//main mapping methods
//sp;lit thru klonm
//support lemmers




//{:timeLimit 30}
lemma {:timeLimit 30} CLONING_PRESERVES_OWNERSHIP(oo : Owner, ob : Bound, co : Owner, cb : Bound, m : Klon)
 //is this name OVERKILL???
 //should it also do bounds?  --- currentlyt NO!
  requires AllReady(flatten(oo))
  requires AllReady(flatten(ob))
  requires AllReady(flatten(co))
  requires AllReady(flatten(cb))
  requires klonCalid(m)
  requires m.m.Keys >= oo
  requires m.m.Keys >= ob

  requires co == mapThruKlon(oo, m)
  requires cb == mapThruKlon(ob, m)

  requires flatten(oo) >= flatten(ob)
  requires stupidlyHappy(oo,ob,m.o) //GRRRRR do we ereally want / need this?   GRRRRRR
 // requires boundsOK(oo,ob) ////HMM do we *always* need this? or not?
 //problem with keeping boundsOK here is that it means we can' use this to prove boundsOK  properlylater...
  //                          ////I'm not sure we do, e.g. the below :-)
  //                          ///our shoudl we unify this with stupidlyHappy??


   ensures flatten(co) >= flatten(cb)
  //  ensures stupidlyHappy(oo,ob,m.o) ==> stupidlyHappy(co,cb,m.c)
  //  ensures boundsOK(oo,ob) ==> boundsOK(co,cb)
{
//  assert (forall o <- oo :: flatten(o.ownerBound()) >= flatten(ob));
      assert m.o.Ready();      assert m.c.Ready();

     var ooSP := flownerSplit(oo, m.o);
  // UNPACK_flownerSplitOK(oo,m.o,ooSP);

     var coSP := flownerSplit(co, m.c);
  // UNPACK_flownerSplitOK(co,m.c,coSP);

     var obSP := flownerSplit(ob, m.o);
  // UNPACK_flownerSplitOK(ob,m.o,obSP);

     var cbSP := flownerSplit(cb, m.c);
  // UNPACK_flownerSplitOK(cb, m.c, cbSP);

  // flownerAll_MONOTONIC(oo,ob,m.o);
  // flownerAll_SONOMONIC_AND_HAPPY_AND_BOUNDS(oo,ooSP,ob,obSP,m.o);

// ////////////////////////////////////////////////////////////
// //oo to co - inside
//  //  //  //  //  //  //  //  //  //  //  //  //  //  //
  //  assert AllReady(obSP.fAll);
  //  assert AllReady(coSP.fAll);
  //  assert klonCalid(m);
  //  assert oo <= m.m.Keys;
  //  assert AllReady(mapThruKlon(oo,m));
  //  assert co == mapThruKlon(oo,m);
  //  assert flownerSplitOK(oo, m.o,ooSP);
  //  assert flownerSplitOK(co, m.c,coSP);
//  //  //  //  //  //  //  //  //  //  //  //  //  //  //
MAPPING_INSIDE(oo,ooSP,co,coSP,m);
MAPPING_INSIDE(ob,obSP,cb,cbSP,m);
// ////////////////////////////////////////////////////////////
// //outside

MAPPING_OUTSIDE(oo,ooSP,co,coSP,m);
MAPPING_OUTSIDE(ob,obSP,cb,cbSP,m);
//

//////////////////////////////////////////////////////////
// the pivot
  //
  // MAP_THRU_KLON(oo,co,m);
  // MAP_THRU_KLON(ob,cb,m);
  //

  UNPACK_flownerSplitOK(oo,m.o,ooSP);
  UNPACK_flownerSplitOK(ob,m.o,obSP);
  UNPACK_flownerSplitOK(co,m.c,coSP);
  UNPACK_flownerSplitOK(cb,m.c,cbSP);

     MAPPING_PIVOT(oo,ooSP,co,coSP,m);    ///  look  ///
     MAPPING_PIVOT(ob,obSP,cb,cbSP,m);   ///  here  ///

     DOUBLE_SPLIT_OnlyPivot(oo, co, ooSP, coSP, m);
//STUPIDLY_HAPPY_To_OnlyPivot(oo,ob,ooSP,obSP,m.o);
     DOUBLE_SPLIT_OnlyPivot(ob, cb, obSP, cbSP, m);


  assert AllReady(flatten(co)) && AllReady(flatten(cb));

ONLY_PIVOT(oo,m.o,ooSP.fPvt);
ONLY_PIVOT(ob,m.o,obSP.fPvt);
ONLY_PIVOT(co,m.c,coSP.fPvt);
ONLY_PIVOT(cb,m.c,cbSP.fPvt);

// / / / / / / / / / / / / / / / / / / / / / / / / / / / / / / / /


  assert ooSP.fSin >= obSP.fSin;
  M4K(ooSP.fSin, obSP.fSin, coSP.fSin, cbSP.fSin, m);
  assert coSP.fSin >= cbSP.fSin;



  assert coSP.fSin >= cbSP.fSin;
//  assert coSP.fOut >= cbSP.fOut;
  assert coSP.fPvt >= cbSP.fPvt;
//  assert coSP.fXpt >= cbSP.fXpt;
   assert coSP.fOut+coSP.fXpt >= cbSP.fOut+cbSP.fXpt;


  assert flownerStrictlyInside(co,m.c) >= flownerStrictlyInside(cb,m.c);

  assert (flownerOutsidePivot(co,m.c) + flownerStrictlyOutside(co,m.c)) >= (flownerOutsidePivot(cb,m.c) + flownerStrictlyOutside(cb,m.c));


FLOWER_JOIN_All(co,cb,m.c);

assert coSP.fAll >= cbSP.fAll;
assert flatten(co) >= flatten(cb);
// assert (forall o <- co :: flatten(o.ownerBound()) >= flatten(cb));
// assert boundsOK(co,cb);
// assert (forall r <- cb | outside(r,m.c) :: exists s <- co :: outside(s,m.c) && inside(s,r));
//
// assert stupidlyHappy(co,cb, m.o);
// flownerAll_SONOMONIC_AND_HAPPY_AND_BOUNDS(co,coSP,cb,cbSP,m.c);


return;

}






//{:timeLimit 30}
lemma CLONING_PRESERVES_BOUNDS(oo : Owner, ob : Bound, co : Owner, cb : Bound, m : Klon)
  requires AllReady(flatten(oo))
  requires AllReady(flatten(ob))
  requires AllReady(flatten(co))
  requires AllReady(flatten(cb))
  requires klonCalid(m)
  requires m.m.Keys >= oo
  requires m.m.Keys >= ob

  requires co == mapThruKlon(oo, m)
  requires cb == mapThruKlon(ob, m)

  requires flatten(oo) >= flatten(ob)
  requires stupidlyHappy(oo,ob,m.o)
  requires boundsOK(oo,ob)

   ensures flatten(co) >= flatten(cb)
   ensures boundsOK(oo,ob)
  //  ensures stupidlyHappy(co,cb,m.c)
{
   CLONING_PRESERVES_OWNERSHIP(oo,ob,co,cb,m);

        // assert (forall r <- ob | outside(r,m.o) :: exists s <- oo :: outside(s,m.o) && inside(s,r));
        // assert flatten(co) >= flatten(cb);
        // assert (forall r <- cb ::  exists o <- ob :: m.m[o] == r);
        // assert (forall r <- co ::  exists o <- oo :: m.m[o] == r);
        // assert (forall r <- cb | outside(r,m.c) :: exists s <- co :: outside(s,m.c) && inside(s,r));

        assert (forall o <- oo :: flatten(o.ownerBound()) >= flatten(ob));

forall o <- oo ensures (flatten(m.m[o].ownerBound()) >= flatten(cb)) //by
   {

// Error: this is the precondition that could not be proved
// Inside strictlyInside(o,m.o)
// Could not prove: part.AMFO > whole.AMFO
// This is the only assertion in batch #360 of 371 in method CLONING_PRESERVES_BOUNDS
// Batch #360 resource usage: 41.9M RU

    CLONING_PRESERVES_OWNERBOUND(o, ob, m.m[o], cb, m);
   }

        assert (forall c <- co :: flatten(c.ownerBound()) >= flatten(cb));
   assert boundsOK(co,cb);
  //  assert stupidlyHappy(co,cb,m.c);

}


lemma CLONING_PRESERVES_OWNERBOUND(o : Object, ob : Owner, c : Object, cb : Owner, m : Klon)
 requires klonCalid(m)
  requires m.objectInKlon(o)
  requires c == m.m[o]
  requires strictlyInside(o,m.o)  ///HHMMMMM

  requires AllReady(flatten(ob))
  requires AllReady(flatten(cb))
  requires m.m.Keys >= ob
  requires cb == mapThruKlon(ob, m)

  requires flatten(o.ownerBound()) >= flatten(ob)

   ensures flatten(c.ownerBound()) >= flatten(cb)
{
assume  flatten(o.ownerBound()) <= m.m.Keys;
assume  flatten(ob) <= m.m.Keys;
assume  boundsOK(o.ownerBound(),ob);

MAPPEN_ONE(o,m);

CLONING_PRESERVES_OWNERSHIP(o.ownerBound(),ob, c.ownerBound(),cb , m);

       assert flatten(c.ownerBound()) >= flatten(cb);
}


lemma OWNER_BOUND_BOUND(o : Object)
 requires o.Ready()
  ensures AllReady( o.ownerBound() )
  ensures (o.owner == o.bound) ==> (o.ownerBound() == {o})
  ensures (o.owner != o.bound) ==> (o.ownerBound() == o.bound)
{}

























lemma MAPPING_INSIDE(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
   requires AllReady(os_sp.fAll)
   requires AllReady(cs_sp.fAll)
   requires klonCalid(m)
   requires os <= m.m.Keys
   requires AllReady(mapThruKlon(os,m))
   requires cs == mapThruKlon(os,m)
   requires flownerSplitOK(os, m.o,os_sp)
   requires flownerSplitOK(cs, m.c,cs_sp)

    ensures mapThruKlon(os_sp.fSin, m) == cs_sp.fSin

{
  assert collectStrictlyInside(os,m.o) <= m.m.Keys;

  assert os_sp.fSin == flownerStrictlyInside(os_sp.soup,m.o);
  assert cs_sp.fSin == flownerStrictlyInside(cs_sp.soup,m.c);

  assert os_sp.fSin == flownerStrictlyInside(os,m.o);
  assert cs_sp.fSin == flownerStrictlyInside(mapThruKlon(os,m),m.c);

FLOWNER_ALL_COLLECT_StrictlyInside(os_sp.soup,m.o);
assert collectStrictlyInside(os_sp.soup,m.o) == flownerStrictlyInside(os_sp.soup,m.o) == os_sp.fSin;
FLOWNER_ALL_COLLECT_StrictlyInside(cs_sp.soup,m.c);
assert collectStrictlyInside(cs_sp.soup,m.c) == flownerStrictlyInside(cs_sp.soup,m.c) == cs_sp.fSin;

MASTERY_THRU(os_sp.soup,m);

 assert mapThruKlon(collectStrictlyInside(os,m.o),m) == collectStrictlyInside(mapThruKlon(os,m),m.c);
 assert mapThruKlon(os_sp.fSin, m) == mapThruKlon(collectStrictlyInside(os,m.o),m);
 assert cs_sp.fSin == flownerStrictlyInside(mapThruKlon(os,m),m.c);
 assert mapThruKlon(os_sp.fSin, m) == cs_sp.fSin;

 }



lemma {:timeLimit 15} MAPPING_PIVOT(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
   requires AllReady(flatten(os))
   requires AllReady(flatten(cs))
   requires m.o.Ready()
   requires m.c.Ready()
   requires klonCalid(m)
   requires flatten(os) <= m.m.Keys
   requires flownerSplitOK(os, m.o,os_sp)
   requires flownerSplitOK(cs, m.c,cs_sp)

   requires os <= m.m.Keys
   requires cs == mapThruKlon(os,m)

   requires os_sp.fPvt == flownerOnlyPivot(os,m.o)
   requires cs_sp.fPvt == flownerOnlyPivot(cs,m.c)

    ensures forall o <- os_sp.fPvt  :: klonLine(o,m.m[o],m)
    ensures forall o <- os_sp.fPvt  :: klonGeometry(o,m.m[o],m)
    ensures forall o <- os_sp.fPvt  :: klonIdentity(o,m.m[o],m)


    ensures if (m.o in flownerAll(os))
              then ((os_sp.fPvt == m.o.AMFO) && (cs_sp.fPvt == m.c.AMFO))
              else ((os_sp.fPvt == {})       && (cs_sp.fPvt == {}))

//     ensures (os_sp.fPvt == {})  <==> (cs_sp.fPvt == {})
//     ensures (os_sp.fPvt == m.o.AMFO) <==> (cs_sp.fPvt == m.c.AMFO)
    // ensures woodCrap(m.o,m.c,m)
{
     assert cs_sp == splitThruKlon(os,os_sp,m);
     MAP_THRU_KLON(os,cs,m);
     UNPACK_flownerSplitOK(mapThruKlon(os,m),m.c,cs_sp);
    //  WOOD_CRAP(m.o,m.c,m);

    flownerOnlyPivot_RESULT(os,m.o,os_sp.fPvt);
    flownerOnlyPivot_RESULT(cs,m.c,cs_sp.fPvt);

     ONLY_PIVOT(os,m.o,os_sp.fPvt);
     ONLY_PIVOT(cs,m.c,cs_sp.fPvt);
}
















lemma MAPPING_OUTSIDE(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
//see HACKKING_THRU -
//
   requires AllReady(os_sp.fAll)
   requires AllReady(cs_sp.fAll)
   requires klonCalid(m)

   requires os <= m.m.Keys // requires m.allInKlon(os)
   requires cs == mapThruKlon(os,m)
   requires flownerSplitOK(os,m.o,os_sp)
   requires flownerSplitOK(cs,m.c,cs_sp)
   requires forall o <- os_sp.fOut :: outside(o, m.o) //left out & recalcualted below

    ensures forall o <- os :: klonLine(o,m.m[o],m)
    ensures forall o <- os :: klonGeometry(o,m.m[o],m)
    ensures forall o <- os :: klonIdentity(o,m.m[o],m)
    ensures forall o : Object <- (os_sp.fOut + os_sp.fXpt) :: outside(o,m.o) && (o == m.m[o] != m.o)

//    ensures forall o <- (os_sp.fOut + os_sp.fXpt) :: woodReal(o,m.m[o],m)
    ensures os_sp.fOut + os_sp.fXpt == cs_sp.fOut + cs_sp.fXpt


//this is the older verison
//
//    requires AllReady(os_sp.fAll)
//    requires AllReady(cs_sp.fAll)
//    requires klonCalid(m)
//
//    requires os <= m.m.Keys
//    requires forall o <- os_sp.fOut :: outside(o, m.o)
//    requires cs == mapThruKlon(os,m)
//    requires flownerSplitOK(os, m.o,os_sp)
//    requires flownerSplitOK(cs, m.c,cs_sp)
//
//
//
//     ensures forall o <- os :: klonLine(o,m.m[o],m)
//     ensures forall o <- os :: klonGeometry(o,m.m[o],m)
//     ensures forall o <- os :: klonIdentity(o,m.m[o],m)
//     ensures forall o : Object <- (os_sp.fOut) :: outside(o,m.o) && (o == m.m[o] != m.o)
//     // ensures forall o : Object <- (os_sp.fOut) :: o.owner == m.m[o].owner
//     // ensures forall o : Object <- (os_sp.fOut) :: o.bound == m.m[o].bound
//     ensures forall o : Object <- (os_sp.fXpt) :: outside(o,m.o) && (o == m.m[o] != m.o)
//     // ensures forall o : Object <- (os_sp.fXpt) :: o.owner == m.m[o].owner
//     // ensures forall o : Object <- (os_sp.fXpt) :: o.bound == m.m[o].bound
//
//     ensures forall o <- (os_sp.fOut) :: woodReal(o,m.m[o],m)
//     ensures forall o <- (os_sp.fXpt) :: woodReal(o,m.m[o],m)
//     ensures os_sp.fOut == cs_sp.fOut
//     ensures os_sp.fXpt == cs_sp.fXpt
{
     assert cs_sp == splitThruKlon(os,os_sp,m);
     MAP_THRU_KLON(os,cs,m);
     UNPACK_flownerSplitOK(mapThruKlon(os,m),m.c,cs_sp);

     var os_Out := os_sp.fOut;
     var cs_Out := cs_sp.fOut;
     assert os_Out == flownerStrictlyOutside(os,m.o);
     assert cs_Out == flownerStrictlyOutside(cs,m.c);

     var os_Xpt := os_sp.fXpt;
     var cs_Xpt := cs_sp.fXpt;
     assert os_Xpt == flownerExceptPivot(os,m.o);
     assert cs_Xpt == flownerExceptPivot(cs,m.c);

    assert AllReady(os_sp.fAll);
    assert AllReady(cs_sp.fAll);
    assert klonCalid(m);
    assert os <= m.m.Keys;

  //  assert AllReady(flatten(os));
  //  assert AllReady(flatten(cs));
  //  assert AllReady(flatten(os_sp.fOut));
  //  assert AllReady(flatten(cs_sp.fOut));
  //  assert AllReady(flatten(os_sp.fXpt));
  //  assert AllReady(flatten(cs_sp.fXpt));
  //  assert klonCalid(m);
  //  assert os      <= m.m.Keys;
  //  assert os_sp.fOut <= m.m.Keys;
  //  assert os_sp.fXpt <= m.m.Keys;
//
//   MAP_THRU_KLON(os,cs,m);
//   assert forall o <- cs | outside(o,m.c) :: (o == m.m[o]);




   assert forall o <- os_sp.fOut :: outside(o, m.o);


   assert forall o <- cs_sp.fOut :: (outside(o,m.c));
   assert forall o <- cs_sp.fOut :: exists k <- m.m.Keys :: klonLine(k,o,m);
   assert forall o <- cs_sp.fOut :: exists k <- m.m.Keys :: (m.m[k] == o)  && (outside(k,m.o)) && (k == o);
   assert forall o <- cs_sp.fOut :: m.m[o] == o;




   assert forall o <- os_sp.fXpt :: outside(o, m.o);





    assert os_sp.fOut >= cs_sp.fOut;
    assert os_sp.fXpt >= cs_sp.fXpt;
    assert os_sp.fOut <= cs_sp.fOut;
    assert os_sp.fXpt <= cs_sp.fXpt;




//    FOREST_REAL(os, os_sp,cs,cs_sp,m); //do I even need this?


}








lemma HACKING_OUTSIDE(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
//see HACKKING_THRU -
//
 ///quick hack at combining fOUT and fXpt - so we don't need to track the outsideness of the soup, or something.
 ///I think the point is that an owner O >= B  should be OK even if  the "strictly ourside" owners in B
 //i.e things reachable from the soup *wihtout8 being inside the pivot
 //well O could be one owner that *is* inside the pivot which is inside Bl..
 //
 //  e.g. bound =   (pivot, someFullyExyernalObject)
 //  intermrdiate has owners =  (pivot, someFullyExyernalObject)
 //  bottom inherits from intermediate  (see notes) 0n
 //

   requires AllReady(os_sp.fAll)
   requires AllReady(cs_sp.fAll)
   requires klonCalid(m)

   requires m.allInKlon(os)
   requires cs == mapThruKlon(os,m)
   requires flownerSplitOK(os,m.o,os_sp)
   requires flownerSplitOK(cs,m.c,cs_sp)

    ensures forall o <- os :: klonLine(o,m.m[o],m)
    ensures forall o <- os :: klonGeometry(o,m.m[o],m)
    ensures forall o <- os :: klonIdentity(o,m.m[o],m)
    ensures forall o : Object <- (os_sp.fOut + os_sp.fXpt) :: outside(o,m.o) && (o == m.m[o] != m.o)

//    ensures forall o <- (os_sp.fOut + os_sp.fXpt) :: woodReal(o,m.m[o],m)
    ensures os_sp.fOut + os_sp.fXpt == cs_sp.fOut + cs_sp.fXpt
{
     assert cs_sp == splitThruKlon(os,os_sp,m);
     MAP_THRU_KLON(os,cs,m);
     UNPACK_flownerSplitOK(os,m.o,os_sp);

     assert (os_sp.fOut + os_sp.fXpt) <= os_sp.fAll <= m.m.Keys;

     assert forall o : Object <- (os_sp.fOut + os_sp.fXpt) :: outside(o,m.o) && (o == m.m[o] != m.o);

     UNPACK_flownerSplitOK(mapThruKlon(os,m),m.c,cs_sp);
     var os_Out := os_sp.fOut + os_sp.fXpt;
     var cs_Out := cs_sp.fOut + cs_sp.fXpt;
     assert os_Out == flownerStrictlyOutside(os,m.o) + flownerExceptPivot(os,m.o);
     assert cs_Out == flownerStrictlyOutside(cs,m.c) + flownerExceptPivot(cs,m.c);


    assert AllReady(os_sp.fAll);
    assert AllReady(cs_sp.fAll);
    assert klonCalid(m);
    assert os <= m.m.Keys;


   assert forall o <- os_sp.fOut :: outside(o, m.o);
   assert forall o <- os_sp.fOut :: m.m[o] == o;

   assert forall o <- cs_sp.fOut :: (outside(o,m.c));
   assert forall o <- cs_sp.fOut :: m.m[o] == o;
   assert forall o <- cs_sp.fOut :: exists k <- m.m.Keys :: klonLine(k,o,m);
   assert forall o <- cs_sp.fOut :: exists k <- m.m.Keys :: (m.m[k] == o)  && (outside(k,m.o)) && (k == o);

    assert forall o <- os_sp.fXpt :: outside(o, m.o);



    assert os_sp.fOut >= cs_sp.fOut;
    assert os_sp.fXpt >= cs_sp.fXpt;
    assert os_sp.fXpt == cs_sp.fXpt;

    assert os_sp.fOut <= cs_sp.fOut;
    assert os_sp.fXpt <= cs_sp.fXpt;
    assert os_sp.fXpt == cs_sp.fXpt;

    assert os_sp.fOut + os_sp.fXpt >= cs_sp.fOut + cs_sp.fXpt;
    assert os_sp.fOut + os_sp.fXpt <= cs_sp.fOut + cs_sp.fXpt;
    assert os_sp.fOut + os_sp.fXpt == cs_sp.fOut + cs_sp.fXpt;

//    FOREST_REAL(os, os_sp,cs,cs_sp,m); //do I even need this?

}

//
//
//
//     assert os_sp.fXpt >= cs_sp.fXpt;
//     assert os_sp.fXpt <= cs_sp.fXpt;
//     assert os_sp.fOut + os_sp.fXpt == cs_sp.fOut + cs_sp.fXpt;






lemma HACKING_THRU(oo : Owner, m : Klon)

 //this versionn adapted from MASTERTY_THRU for some reason1
  decreases allAMFOs(oo), 15
   requires klonCalid(m)
   requires m.allInKlon(oo)
   requires AllReady(oo)
   requires AllReady(mapThruKlon(oo,m))

  //  ensures  (flownerStrictlyOutside(oo,m.o) + flownerExceptPivot(oo,m.o)) ==
  //  (flownerStrictlyOutside(mapThruKlon(oo,m),m.c) + flownerExceptPivot(mapThruKlon(oo,m),m.c))
{
  assert oo <= m.m.Keys;
  assert flownerAll(oo) == flatten(oo) <= m.m.Keys;
  var cc := (mapThruKlon(oo,m));
  var fOX := (flownerStrictlyOutside(oo,m.o) + flownerExceptPivot(oo,m.o));
  var mOX := (flownerStrictlyOutside(cc,m.c) + flownerExceptPivot(cc,m.c));

  assert flownerStrictlyOutside(oo,m.o) <= flownerAll(oo);
  assert flownerExceptPivot(oo,m.o) <= flownerAll(oo);
  assert fOX <= flownerAll(oo) == flatten(oo) <= m.m.Keys;

  assert forall o <- flownerStrictlyOutside(oo,m.o) :: outside(o,m.o);
  assert forall o <- flownerExceptPivot(oo,m.o) :: outside(o,m.o);
  assert forall o <- fOX :: outside(o,m.o);
  assert forall o <- fOX :: m.m[o] == o;

assert flownerStrictlyOutside(cc,m.c) == mtk(flownerStrictlyOutside(oo,m.o), m);
assert flownerExceptPivot(cc,m.c) == mtk(flownerExceptPivot(oo,m.o), m);

//  assert mOX == mapThruKlon(fOX,m);

//  MAP_KLON_IDENTITY(fOX,mOX,m);
//
//   assert forall o <- flownerStrictlyOutside(oo,m.o) :: o in flownerStrictlyOutside(cc,m.c);
//   assert forall o <- flownerStrictlyOutside(cc,m.c) :: o in flownerStrictlyOutside(oo,m.o);
//   assert flownerStrictlyOutside(oo,m.o) <= flownerStrictlyOutside(cc,m.c);
//   assert flownerStrictlyOutside(oo,m.o) >= flownerStrictlyOutside(cc,m.c);
//   SetLtGtEq(flownerStrictlyOutside(oo,m.o),flownerStrictlyOutside(cc,m.c));
//   assert flownerStrictlyOutside(oo,m.o) == flownerStrictlyOutside(cc,m.c);
//
//
//   assert forall o <- flownerExceptPivot(oo,m.o) :: o in flownerExceptPivot(cc,m.c);
//   assert forall o <- flownerExceptPivot(cc,m.c) :: o in flownerExceptPivot(oo,m.o);
//   assert flownerExceptPivot(oo,m.o) <= flownerExceptPivot(cc,m.c);
//   assert flownerExceptPivot(oo,m.o) >= flownerExceptPivot(cc,m.c);
//   assert flownerExceptPivot(oo,m.o) == flownerExceptPivot(cc,m.c);
//
//   assert forall o <- flownerStrictlyOutside(oo,m.o) :: outside(o,m.o);
//   assert forall o <- flownerExceptPivot(oo,m.o) :: outside(o,m.o);
//   assert forall c <- flownerStrictlyOutside(cc,m.c) :: outside(c,m.c);
//   assert forall c <- flownerExceptPivot(cc,m.c) :: outside(c,m.c);
//
//   forall o <- fOX ensures ((m.m[o] == o) && (m.m[o] in mOX))
//     {
//       var c := m.m[o];
//       assert klonLine(o,c,m);
//       assert klonGeometry(o,c,m);
//       assert klonIdentity(o,c,m);
//       assert outside(o,m.o);
//       assert c == o;
//     }

  // assert fOX == mOX;
  // assert (flownerStrictlyOutside(oo,m.o) + flownerExceptPivot(oo,m.o)) ==
  //    (flownerStrictlyOutside(mapThruKlon(oo,m),m.c) + flownerExceptPivot(mapThruKlon(oo,m),m.c));
//  assert flownerDisjunctPivot(oo,m.o) == flownerDisjunctPivot(cc,m.c);
}























lemma {:timeLimit 60} MASTERY_OBJECT(o : Object, m : Klon)
  decreases o.AMFO, 14
   requires o.Ready()
   requires klonCalid(m)
   requires m.objectInKlon(o)
   requires collectObjectStrictlyInside(o,m.o) <= m.m.Keys

    ensures mapThruKlon(collectObjectStrictlyInside(o,m.o),m) == collectObjectStrictlyInside(m.m[o],m.c)
{
   var c  := m.m[o];
   var mc := mapThruKlon(collectObjectStrictlyInside(o,m.o),m);
   var cm := collectObjectStrictlyInside(c,m.c);

  if (not(strictlyInside(o,m.o)))
    {
      assert (not(strictlyInside(c,m.c)));
      assert collectObjectStrictlyInside(o,m.o) == {};
      assert mapThruKlon(collectObjectStrictlyInside(o,m.o),m) == {};
      assert collectObjectStrictlyInside(c,m.c) == {};
      assert {} == mc == cm;
      return;
    }

  assert (strictlyInside(o,m.o));
  assert (strictlyInside(c,m.c));

  assert collectObjectStrictlyInside(o,m.o) == {o} + collectStrictlyInside(o.owner,m.o)
      by {
        assert collectObjectStrictlyInside(o,m.o) == (if (not(strictlyInside(o,m.o))) then ({}) else ({o}+collectStrictlyInside(o.owner,m.o)));
        assert (strictlyInside(o,m.o));
        assert collectObjectStrictlyInside(o,m.o) == {o} + collectStrictlyInside(o.owner,m.o);
      }

  assert collectObjectStrictlyInside(c,m.c) == {c} + collectStrictlyInside(c.owner,m.c);
  assert cm == {c} + collectStrictlyInside(c.owner,m.c);

  assert mapThruKlon(collectObjectStrictlyInside(o,m.o),m)
     == mapThruKlon({o}  + collectStrictlyInside(o.owner,m.o),m)
     == mapThruKlon({o},m) + mapThruKlon(collectStrictlyInside(o.owner,m.o),m)
     == {c} + mapThruKlon(collectStrictlyInside(o.owner,m.o),m)
       by {
            FLATTEN_SUMS(
              {o},  collectStrictlyInside(o.owner,m.o),
             ({o} + collectStrictlyInside(o.owner,m.o)),
              m);
            MAPPEN_ONE(o,m);
       }

  assert mc == {c} + mapThruKlon(collectStrictlyInside(o.owner,m.o),m);

  assert c.owner == mapThruKlon(o.owner, m) by
    { assert klonLine(o,c,m);
      assert klonIdentity(o,c,m);
      assert strictlyInside(o,m.o);
      assert o != m.o;
      assert c.owner == mapThruKlon(o.owner, m);
    }

  assert cm == {c} + collectStrictlyInside(mapThruKlon(o.owner, m),m.c);

  MASTERY_THRU(o.owner, m);

  assert       mapThruKlon(collectStrictlyInside(o.owner,m.o),m) ==       collectStrictlyInside(mapThruKlon(o.owner, m),m.c);
  assert {c} + mapThruKlon(collectStrictlyInside(o.owner,m.o),m) == {c} + collectStrictlyInside(mapThruKlon(o.owner, m),m.c);

  assert mc == cm;
  assert mapThruKlon(collectObjectStrictlyInside(o,m.o),m) == collectObjectStrictlyInside(m.m[o],m.c);
}


lemma {:timeLimit 10} MASTERY_THRU(oo : Owner, m : Klon)
  decreases allAMFOs(oo), 15
   requires klonCalid(m)
   requires m.allInKlon(oo)
   requires AllReady(oo)
   requires AllReady(mapThruKlon(oo,m))
   requires oo <= m.m.Keys

    ensures mapThruKlon(collectStrictlyInside(oo,m.o),m) == collectStrictlyInside(mapThruKlon(oo,m),m.c)
{
   assert collectStrictlyInside(oo,m.o) <= m.m.Keys;

  var mc := mapThruKlon(collectStrictlyInside(oo,m.o),m);
  var cm := collectStrictlyInside(mapThruKlon(oo,m),m.c);

  forall o <- oo ensures (mapThruKlon(collectObjectStrictlyInside(o,m.o),m) == collectObjectStrictlyInside(m.m[o],m.c))
      {
      var c := m.m[o];
      var omc := mapThruKlon(collectObjectStrictlyInside(o,m.o),m);
      var ocm := collectObjectStrictlyInside(m.m[o],m.c);
      assert o.Ready();
      assert klonCalid(m);
      assert m.objectInKlon(o);
      assert c == m.m[o];
      assert collectObjectStrictlyInside(o,m.o) <= m.m.Keys;



      MASTERY_OBJECT(o, m) by {
                                GOING_DOWN(oo,o);
                                assert (allAMFOs(oo),15 decreases to o.AMFO,14);
                              }
      assert (mapThruKlon(collectObjectStrictlyInside(o,m.o),m) == collectObjectStrictlyInside(m.m[o],m.c));
      }

   assert mc == cm;
   assert mapThruKlon(collectStrictlyInside(oo,m.o),m) == collectStrictlyInside(mapThruKlon(oo,m),m.c);

}






lemma M4K(os : Owner, ob : Owner, cs : Owner, cb : Owner, m : Klon)
 // this is technically *wrong* or rather it's not the whole story
 // you can't make the arguments just the whole lot and call it done!
 // the mainline is flatten(os) >= flatten(ob) for starters
 // but if we can't get this, we can't get the rest.
 // this shoudl work on "inside" which is the one thing currently missing...
 //
 //in spite of that long long rant above - it ran first time 3 Oct 2026
 //
  // requires AllReady(os)  //actually
  // requires AllReady(ob)
  // requires AllReady(cs)
  // requires AllReady(cb)

  requires m.m.Keys >= os
  requires m.m.Keys >= ob

  requires os >= ob
  requires cs == mtk(os,m)  // or should this be woodFood someting-or-othetr
  requires cb == mtk(ob,m)

   ensures cs >= cb
{}




























lemma INSIDE_PARALLEL(o0 : Object, o1 : Object, c0 : Object, c1 : Object, m : Klon)
 // o0 & o1 are inside the pivot; cloned to c0 and c1
 // o0 is inside o1; ensures c0 inside c1...
 //  "CLXNING_PRESERVES_INSIDE"??
 decreases o0.AMFO
  requires o0.Ready()
  requires o1.Ready()
  requires c0.Ready()
  requires c1.Ready()
  requires o0 in m.m.Keys
  requires o1 in m.m.Keys
  requires klonCalid(m)
  requires c0 == m.m[o0]
  requires c1 == m.m[o1]

  requires strictlyInside(o0,m.o)
  requires strictlyInside(o1,m.o)
  requires inside(o0,o1)

   ensures strictlyInside(c0,m.c)
   ensures strictlyInside(c1,m.c)
   ensures inside(c0,c1)

  {
    if (o0 == o1) { assert o0 == o1;           assert inside(o0,o1);
                    assert m.m[o0] == m.m[o1]; assert inside(c0,c1);
                    return;  }

    assert o0 != o1;     assert c0 != c1;

    //shoudl this also be WOOD_FOOD?  - is the c0.owner conclusion the important one?
    assert klonLine(o0,c0,m);
    assert klonIdentity(o0,c0,m);
    assert (o0 != m.o) && (not(outside(o0,m.o)));
    assert strictlyInside(c0,m.c);
    assert (o0 != m.o) && (o0 != c0);
    assert c0.owner == mapThruKlon(o0.owner,m);

    if (o1 in o0.owner)
      {
        assert c1 in c0.owner;
        assert inside(c0,c1);
        return;
      }

    assert inside(o0,o1);
    ThereIsALightThatNeverGoesOut(o0,o1);
    var oo := YouCan'tGetThereFromHereBut(o0,o1);
    INSIDE_PARALLEL(oo,o1,m.m[oo],c1,m);
  }



lemma CARREFOUR(
      oo : Owner, oo_sp : FlownerSplit, ob : Bound, ob_sp : FlownerSplit,
      co : Owner, co_sp : FlownerSplit, cb : Bound, cb_sp : FlownerSplit,
      m  : Klon)
  requires klonCalid(m)

  requires flownerAll(oo) >= flownerAll(ob)
  requires stupidlyHappy(oo,ob,m.o)
  requires boundsOK(oo,ob)

  ensures oo_sp.fAll >= ob_sp.fAll
  ensures oo_sp.fSin >= ob_sp.fSin

  requires AllReady(flatten(oo))
  requires AllReady(flatten(ob))
  requires m.o.Ready()
  requires flownerSplitOK(oo,m.o,oo_sp)
  requires flownerSplitOK(ob,m.o,ob_sp)

  requires AllReady(flatten(co))
  requires AllReady(flatten(cb))
  requires m.c.Ready()
  requires flownerSplitOK(co,m.c,co_sp)
  requires flownerSplitOK(cb,m.c,cb_sp)

  requires oo <= m.m.Keys
  requires ob <= m.m.Keys
  requires co == mtk(oo,m)
  requires cb == mtk(ob,m)

  ensures co_sp == splitThruKlon(oo,oo_sp,m)
  ensures cb_sp == splitThruKlon(ob,ob_sp,m)

//  ensures co_sp.fAll >= cb_sp.fAll
  ensures co_sp.fSin >= cb_sp.fSin

  //  ensures stupidlyHappy(co,cb,m.c)
  //  ensures boundsOK(co,cb)

{
  assert co_sp == splitThruKlon(oo,oo_sp,m);
  assert cb_sp == splitThruKlon(ob,ob_sp,m);

  MAP_THRU_KLON(oo,co,m);
  MAP_THRU_KLON(ob,cb,m);

  UNPACK_flownerSplitOK(oo,m.o,oo_sp);
         assert oo_sp.fSin == flownerStrictlyInside(oo,m.o);  //Err
  UNPACK_flownerSplitOK(ob,m.o,ob_sp);
         assert ob_sp.fSin == flownerStrictlyInside(ob,m.o);  //Err
  UNPACK_flownerSplitOK(co,m.c,co_sp);
         assert co_sp.fSin == flownerStrictlyInside(co,m.c);  //Err
  UNPACK_flownerSplitOK(cb,m.c,cb_sp);
         assert cb_sp.fSin == flownerStrictlyInside(cb,m.c);  //Err

  assert oo_sp.fAll >= ob_sp.fAll;
  assert forall o <- ob_sp.fAll :: o in oo_sp.fAll;

  flownerStrictlyInside_MONOTONIC(oo,ob,m.o);
//  flownerStrictlyInside_MONOTONIC(co,cb,m.c);  // flownerAll(co) >= flownerAll(cb)
    //hat's very muc hthe wrong thing - tha's what we're trying to PROVE...

  assert oo_sp.fSin >= ob_sp.fSin;
  assert forall o <- ob_sp.fSin :: o in oo_sp.fSin;



  assert oo_sp.fSin >= ob_sp.fSin;

}









lemma FUCKED(o0 : Owner, o1 : Owner, o2 : Owner, b0 : Owner, b1 : Owner, b2 : Owner)
  //set >= monotonic over disjoint splts and through joint sum
  requires o0 >= b0
  requires (o1+o2) >= (b1+b2)
  requires o0 !! (o1+o2)
  requires b0 !! (b1+b2)
   ensures (o0+o1+o2) >= (b0+b1+b2)
   {}



lemma FLOWER_JOIN_All(oo : Owner, ob : Bound, pivot : Object)
 //given the vartious components are >=, conclude Foo >= Fob,
 //just a nice? version of FLOWER_JOIN_H without the typo
  requires AllReady(flatten(oo))
  requires AllReady(flatten(ob))
  requires pivot.Ready()

  requires flownerStrictlyInside(oo,pivot) >= flownerStrictlyInside(ob,pivot)
  requires (flownerOutsidePivot(oo,pivot) + flownerStrictlyOutside(oo,pivot)) >= (flownerOutsidePivot(ob,pivot) + flownerStrictlyOutside(ob,pivot))

   ensures flownerStrictlyInside(oo,pivot) + (flownerOutsidePivot(oo,pivot) + flownerStrictlyOutside(oo,pivot)) >=
           flownerStrictlyInside(ob,pivot) + (flownerOutsidePivot(ob,pivot) + flownerStrictlyOutside(ob,pivot))

   ensures flownerAll(oo) == flownerStrictlyInside(oo,pivot) + (flownerOutsidePivot(oo,pivot) + flownerStrictlyOutside(oo,pivot))
   ensures flownerAll(ob) == flownerStrictlyInside(ob,pivot) + (flownerOutsidePivot(ob,pivot) + flownerStrictlyOutside(ob,pivot))
   ensures flownerAll(oo) >= flownerAll(ob)
//   ensures stupidlyHappy(oo,ob,pivot)
   {
    FUCKED(flownerStrictlyInside(oo,pivot), flownerOutsidePivot(oo,pivot), flownerStrictlyOutside(oo,pivot),
           flownerStrictlyInside(ob,pivot), flownerOutsidePivot(ob,pivot), flownerStrictlyOutside(ob,pivot)) ;
    FLOWNER_DISJOINT(oo, pivot);
    FLOWNER_DISJOINT(ob, pivot);
    FLOWNER_ALL_ALL(oo,pivot);
    FLOWNER_ALL_ALL(ob,pivot);
   }





















function  splitThruKlon(soup : OWNR, split : FlownerSplit, m : Klon) : (cc : FlownerSplit)
 //this doesn't acutally jmove the split across the map
 //**it just recaloculates from scratch? */
 //
 //what I think I meant is (Sep 2026 26)
 //that this returns an OK split
 //but that it does not characterize the relationship
 //between the two slides of the split
  requires AllReady(flatten(soup)) && klonCalid(m)
  requires flownerSplitOK(soup,m.o,split)
  requires split.pivot == m.o
  requires split.soup  == soup
  requires m.m.Keys >= soup
   ensures cc.Valid()
   ensures flownerSplitOK(mapThruKlon(soup,m),m.c,cc)
   reads m.hns()
   {
       var coup := mapThruKlon(soup,m);
       var pivot := m.c;
       var cc := flownerSplit(coup,pivot);
       cc
}




//lemmers




lemma DOUBLE_SPLIT_OnlyPivot(os : Owner, cs : Owner, os_sp : FlownerSplit, cs_sp : FlownerSplit, m : Klon)
 //verified 21Sep2026
  requires AllReady(flatten(os)) && AllReady(flatten(cs))
  requires klonCalid(m)
  requires m.m.Keys >= os
  requires cs == mapThruKlon(os,m)
  requires flownerSplitOK(os, m.o, os_sp)
  requires flownerSplitOK(cs, m.c, cs_sp)
   ensures os_sp.fAll == flownerAll(os)
   ensures cs_sp.fAll == flownerAll(cs)
   ensures os_sp.fPvt == flownerOnlyPivot(os, m.o)
   ensures cs_sp.fPvt == flownerOnlyPivot(cs, m.c)

   ensures (m.o  in os_sp.fAll) ==> (os_sp.fPvt == m.o.AMFO)
   ensures (m.o !in os_sp.fAll) ==> (os_sp.fPvt == {})
   ensures (m.o  in os_sp.fAll) ==> (cs_sp.fPvt == m.c.AMFO)
   ensures (m.o !in os_sp.fAll) ==> (cs_sp.fPvt == {})

//   ensures os_sp.fPvt == (if (m.o in os_sp.fAll) then (m.o.AMFO) else {})
 {
   assert os_sp.fPvt == flownerOnlyPivot(os, m.o);
FLOWNER_SHORTCUT_OnlyPivot(os, m.o, os_sp.fPvt);
   assert os_sp.fPvt == shortcutOnlyPivot(os, m.o);
 LEMMA_shortcutOnlyPivot1(os, m.o, os_sp.fPvt);

   assert (m.o  in os_sp.fAll) ==> (os_sp.fPvt == m.o.AMFO);
   assert (m.o !in os_sp.fAll) ==> (os_sp.fPvt == {});
   if (m.o in os_sp.fAll) { assert os_sp.fPvt == m.o.AMFO; } else { assert os_sp.fPvt == {}; }
//   assert os_sp.fPvt == (if (m.o in os_sp.fAll) then (m.o.AMFO) else {});

  assert (m.o in os_sp.fAll) ==> (m.c in cs_sp.fAll);

   assert cs_sp.fPvt == flownerOnlyPivot(cs, m.c);
FLOWNER_SHORTCUT_OnlyPivot(cs, m.c, cs_sp.fPvt);
   assert cs_sp.fPvt == shortcutOnlyPivot(cs, m.c);
 LEMMA_shortcutOnlyPivot1(cs, m.c, cs_sp.fPvt);

 }

















































lemma collectObjectStrictlyInside_LEMMA1z_noall(o : Object, pivot : Object)
  //if I'm inside I should be in collectObjectStrictlyInside
  //given this one, why do I need all the other shit I'm doing
  //to prove shit?
  //see eg  argh_LEMMA13_noall
  decreases o.AMFO
   requires o.Ready()
   // ensures forall oo <- argh(o) | strictlyInside(oo,pivot) :: oo in collectObjectStrictlyInside(o, pivot)

    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) <= collectObjectStrictlyInside(o, pivot)
    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) >= collectObjectStrictlyInside(o, pivot)
    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) == collectObjectStrictlyInside(o, pivot)

    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) <= arghStrictlyInside(o, pivot)
    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) >= arghStrictlyInside(o, pivot)
    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) == arghStrictlyInside(o, pivot)

    ensures arghStrictlyInside(o,pivot) == collectObjectStrictlyInside(o, pivot)
   {
    forall oo <- argh(o) | strictlyInside(oo,pivot) ensures ( oo in collectObjectStrictlyInside(o, pivot) )  {
       assert o.Ready();
       assert oo in argh(o);
       assert strictlyInside(oo,pivot);
       collectObjectStrictlyInside_LEMMA1o_noall(o,pivot,oo);
       assert oo in collectObjectStrictlyInside(o, pivot);
      }

   forall  oo <- collectObjectStrictlyInside(o, pivot) ensures (oo in (set oo <- argh(o) | strictlyInside(oo,pivot))) {
      assert o.Ready();
      assume oo.Ready();
      assert oo in argh(o);
      assert strictlyInside(oo,pivot);
      assert oo in (set oo <- argh(o) | strictlyInside(oo,pivot));


      }

    }



lemma collectObjectStrictlyInside_LEMMA1o_noall(o : Object, pivot : Object, x : Object)
  //if x is inside x should be in collectObjectStrictlyInside
  decreases o.AMFO, 2
   requires o.Ready()
   requires x in argh(o)
   requires strictlyInside(x,pivot)
    ensures x in collectObjectStrictlyInside(o, pivot)
   {
      if (x == o) {assert x in collectObjectStrictlyInside(o, pivot); return;}
      assert x != o;
      assert exists oo <- o.owner, xx <- argh(oo) :: x == xx;
      assert exists oo <- o.owner :: x in collectObjectStrictlyInside(oo, pivot);
    }





// lemmers


//{:timeLimit 60}
lemma FLOWNER_ALL_COLLECT_StrictlyInside(soup : OWNR, pivot : Object)
 decreases allAMFOs(soup), 2
  requires AllReady(flatten(soup)) && pivot.Ready()
   ensures flownerStrictlyInside(soup,pivot) <= flownerAll(soup)
  //  ensures allStrictlyInside(flatten(soup),pivot) == flownerStrictlyInside(soup,pivot)
  //  ensures allStrictlyInside(flownerAll(soup),pivot) == flownerStrictlyInside(soup,pivot)

   ensures collectStrictlyInside(soup,pivot) == flownerStrictlyInside(soup,pivot)
{
 forall o <- soup
    ensures (flownerStrictlyInside({o},pivot) == collectObjectStrictlyInside(o, pivot)) //by
    { assert allAMFOs(soup) nonincreases to o.AMFO;
      assert 2 decreases to 1;
      assert (allAMFOs(soup),2  nonincreases to o.AMFO,1);
      FLOWNER_ALL_COLLECT_StrictlyInside2(o,pivot); }

 assert forall o <- soup :: collectObjectStrictlyInside(o,pivot) <= collectStrictlyInside(soup,pivot);


 assert forall o <- collectStrictlyInside(soup,pivot) ::
    exists s <- soup :: o in s.AMFO;
 assert forall o <- collectStrictlyInside(soup,pivot) ::
    exists s <- soup :: o in collectObjectStrictlyInside(s,pivot);
//  assert forall o <- collectStrictlyInside(soup,pivot) ::
//     o in (set s <- soup, ss <- collectObjectStrictlyInside(s,pivot) :: ss);

}


lemma FLOWNER_ALL_COLLECT_StrictlyInside2(o : Object, pivot : Object)
 decreases o.AMFO, 1
  requires o.Ready() && pivot.Ready()
   ensures flownerStrictlyInside({o},pivot) == collectObjectStrictlyInside(o, pivot)
 {
   if (not(strictlyInside(o,pivot)))
    {
      assert collectObjectStrictlyInside(o, pivot) == {};
      assert flownerStrictlyInside({o},pivot) == {};
      assert  flownerStrictlyInside({o},pivot) == collectObjectStrictlyInside(o, pivot);
      return;
    }
  assert strictlyInside(o,pivot);
  assert o in flownerStrictlyInside({o},pivot);
  assert o in collectObjectStrictlyInside(o, pivot);
  assert AllReady(flatten(o.owner));
  Object.RettyBetty(o.owner);
  FLOWNER_ALL_COLLECT_StrictlyInside(o.owner,pivot);

  assert flownerStrictlyInside({o},pivot) == collectObjectStrictlyInside(o, pivot);
}






///the magic lines?
// assert forall oo <- soup :: (set ooo <- collectStrictlyInside({oo},pivot) :: ooo) == (set ooo <- flownerStrictlyInside({oo},pivot) :: ooo);
// assert (set oo <- soup, ooo <- (set x <- collectStrictlyInside({oo},pivot)) :: ooo) == (set oo <- soup, ooo <- flownerStrictlyInside({oo},pivot) :: ooo);
// assert (set oo <- soup, ooo <- collectStrictlyInside({oo},pivot) :: ooo) == (set oo <- soup, ooo <- flownerStrictlyInside({oo},pivot) :: ooo);
//























lemma GOING_DOWN(oo : Owner, o : Object)
    requires oo > {}
    requires o in oo
     ensures allAMFOs(oo) >= o.AMFO
     ensures allAMFOs(oo) nonincreases to o.AMFO
     ensures 15 decreases to 14
     ensures (allAMFOs(oo), 15 decreases to o.AMFO, 14)
{}


//forall x <- flatten(soup) && strictlyInside(x,pivot) ::  m.m[x] in flatten(coup) && strictlyInside(m.m[x], other-pivot))
//forall x <- flatten(coup) && strictlyInside(x,pivot) ::  unm(x) in flatten(soup) && strictlyInside(unm(x) , other-pivot))


lemma FLATTEN_ONE(o : Object)
  requires o.Ready()
  ensures flatten({o}) == {o} + flatten(o.owner) == o.AMFO
{}

lemma FLATTEN_SUMS(a : Owner, b : Owner, c : Owner, m : Klon)
  //just say  FLATTEN_SUMS(done,{next},done+{next},m);

  requires a+b == c
  // requires forall o <- a :: o.Ready()  //I'm OH SO TORY
  // requires forall o <- b :: o.Ready()  //I'm OH SO TORY
  // requires forall o <- c :: o.Ready()  //TORY TORY TORY
  //  requires AllReady(a)
  //  requires AllReady(b)
  //  requires AllReady(c)
  //  requires klonReady(m)
  //  requires klonCalid(m)
  requires (a+b+c) <= m.m.Keys
  //    ensures recFlatten(a)+recFlatten(b)==recFlatten(a+b)
  ensures flatten(a) + flatten(b) == flatten(a+b)
  ensures mapThruKlon(a,m) + mapThruKlon(b,m) == mapThruKlon(a+b,m)
  ensures mapThruKlon(a+b,m) == mapThruKlon(a,m) + mapThruKlon(b,m)
  ensures flatten(mapThruKlon(a,m)) + flatten(mapThruKlon(b,m)) == flatten(mapThruKlon(a+b,m))
  ensures flatten(mapThruKlon(a+b,m)) == flatten(mapThruKlon(a,m)) + flatten(mapThruKlon(b,m))
{}



lemma MAPPEN_ONE(o : Object, m : Klon)
 //shitteth has been throwth at the wallth and it sticketh
  requires o.Ready()
  requires o in m.m.Keys
  requires klonReady(m)
  requires klonCalid(m)
   ensures (set x <- {o} :: m.m[x]) == {m.m[o]}
   ensures mtk({o},m) == {m.m[o]}
   ensures mapThruKlon({o},m) == {m.m[o]}
{
  LemmaSingletonSize({o},o);
  assert IsSingleton({o});
  var z := ExtractFromSingleton({o});
  assert z == o;
  assert {z} == {o};
  assert (set x <- {o} :: m.m[x]) == {m.m[o]};
  assert forall x <- {o} :: x == o;
  assert o in m.m.Keys;
  assert {m.m[o]} == (set x <- {o} :: m.m[x]);
  assert mtk({o},m) == {m.m[o]};
  var os := {o};
  MTK_THRU_KLON(os,m);
  assert mapThruKlon(os,m) == mtk(os,m);
}

// lemma MAPPEN_ONE(o : Object, m : Klon)
//  //took at least an hour trying more sensile versions of the next 12 lines
//  //to just copy these ones in from an earlier file because they work.
//   requires o.Ready()
//   requires o in m.m.Keys
//   requires klonReady(m)
//   requires klonCalid(m)
//   ensures mtk({o},m) == {m.m[o]}
// {
//  FLATTEN_ONE(o);
// }
// lemma FLATTEN_ONE(o : Object)
//   requires o.Ready()
//   ensures flatten({o}) == {o} + flatten(o.owner) == o.AMFO
// {}









lemma STRICTLY_OUTSIDE_IN_SOUP(soup : Owner, o : Object, pivot : Object, owner : Object)
  requires AllReady(flatten(soup))
  requires o.Ready()
  requires pivot.Ready()
  requires owner.Ready()
  requires owner in flownerStrictlyOutside(soup, pivot)
  requires inside(o, owner)
  requires o in soup

   ensures forall s <- soup | outside(s,pivot) ::
             forall owner <- s.AMFO | outside(owner,pivot) ::
               owner in flownerStrictlyOutside(soup, pivot)

   // ensures forall s <- soup, owner <- flownerStrictlyOutside(soup, pivot) :: outside(owner,pivot) &&  outside(s,pivot) && inside(s,owner)

   ensures forall owner <- flownerStrictlyOutside(soup, pivot) ::
      exists s <- soup :: (
        && (outside(s,pivot))
        && (outside(owner,pivot))
        && (inside(s,owner))
      )


//   ensures forall owner <- flownerAll(soup) :: exists s <- soup ::  &&

   ensures owner in flatten(soup)
   ensures o in soup
   ensures outside(owner,pivot)
   {
     var Out := (set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerStrictlyOutside(o,pivot,owner) :: owner);
     assert owner in Out;
   }
