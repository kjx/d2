//Xlone_Via_Map -> Xlone_All_Owners, Xlone_Clone_Clone
//Xlone_Clone_Clone -> Xlone_All_Owners, Object.make(), Xlone_All_Fields
//Xlone_All_Owners -> Xlone_Via_Map
//Xlone_All_Fields -> Xlone_Field_Map
//Xlone_Field_Map ->  Xlone_Via_Map, Xlone_Set_Field
//Xlone_Set_Field

//7 Apr 2026  oops! Xlone_All_Owners, Xlone_Set_Field, Xlone_Via_Map all done.
//             Xlone_Clone_Clone, Xlone_Field_Map, completes with errors
//             Xlone_All_Fields CRASHES - but apparently word back in marc
//
//
//7 Apr 2026 - Xlone_Via_Map   time lately verify Xlone.dfy  $GNT  --isolate-assertions --verification-time-limit=15 --filter-position=:100-135
//                             time lately verify Xlone.dfy  $GNT  --isolate-assertions --verification-time-limit=15 --filter-position=:135-177
//6 Feb 2026 - Xlone_Field_Map verifies with 4.11.1+58b3f6aa160b15bf6a76dc4302b3acbb442153ec, real	64m28.760s, user	86m26.281s, --verification-time-limit=7 --isolate-assertions --cores 6  --progress=batch  --dont-verify-dependencies --filter-symbol=Xlone_Field_Map
//6 FEb 2026 - note that the"critical" point is method declrn had "timeLimit: 0" on it.
//19Feb 2026 - Xlone_Via_Map verifies (I think only  "XCC" doesn't verify),  but in two stages   470-498 499-520,  with --verification-time-limit=15
//25Feb 2026 - Xlone_Via_Map  body verifies 470-520. crashes on 466 which is ensures; 520-529 530-533 works...
//active TODOs TRUMP JDVANCE

//TODO NUKEM - fiddling with the bounds settings?

//attempt to fix Xlone_Field_Mgap which doesn't handle the case where
//we've already got the originql field value in the map
//better don't recurse then than that we do...h
//look back at earliuer versions (i or j) to see the bug?

//for later :  this thinks you cnat colone any object into itself.       but.

//3May copying decreases clauses from current X2.dfy in here.

include "Library.dfy"
include "Ownership-Recursive.dfy"
include "Klon.dfy"
include "Printing.dfy"
//include "B2.dfy"
include "Context.dfy"

include "Klon-HighLine.dfy"


include "Xlone_All_Fields.dfy"
include "Xlone_All_Owners.dfy"
include "Xlone_Clone_Clone.dfy"
include "Xlone_Field_Map.dfy"
include "Xlone_Set_Field.dfy"
include "Xlone_Via_Map.dfy"

//commented out version of   XClone_Via_Map deletged Tue 20 Mar 2026
//commented out "ensures HighCalidFragilistic()" from XClone_Via_Map
//added "assert HighCalidFragilistic()" after every call to XClone_Via_Map

////////////////////////////////////////////////////////////////////////////////////////


predicate Xlone_Complete(m : Klon)
  reads m.m.Keys`fields, m.m.Values`fields
 //should be method on Klon?
 //good to have but not acutally neededd for this (or anything?)
 //should be established by Xlone methods (how?)  (dunno?)  (track the variant???)
 {
  forall k <- m.m.Keys ::
    var v := m.m[k];
      || (v == k)
      || (v.fields.Keys == k.fields.Keys)
      || (v.fields.Values <= m.m.Keys)   //what's wgong on here???
         //why not just (v.fields.Keys == k.fields.Keys)
        // true for pivot, inside, and outside if v == k...
 }

////////////////////////////////////////////////////////////////////////////////////////




lemma /*VFF*/ XVM_decreases_to_XCC(a : Object, m' : Klon)
  ensures
   (m'.oHeap - m'.m.Keys + {a}, |a.AMFO|, |a.fields.Keys|, 20 //Klone_Via_Map
    decreases to m'.oHeap - m'.m.Keys + {a}, |a.AMFO|, |a.fields.Keys|, 15)
{}





































predicate flerb(a : Owner, b : Owner) {flatten(a) >= flatten(b)}

lemma  ReadyBounds4(o : Object)
  requires o.Ready()
  ensures  o.AMFO > o.AMFX >= o.AMFB
  ensures  bounds4(o)
{}

predicate  bounds4(o : Object)  { nuBoundsOK(o.owner, o.bound) }                            //NUBOUNDS
 //{ o.AMFO > o.AMFX >= o.AMFB  >= collectBounds(o.AMFX) } //NUBOUNDS


lemma {:isolate_assertions} CalidBounds4(k : Object, m : Klon)
  requires m.CalidOwners()
  requires k.Ready()
  requires strictlyInside(k,m.o)
{
  var o := m.o;
  assert m.o.Ready();
  ReadyBounds4(m.o);
  assert o.AMFO > o.AMFX >= o.AMFB; //NIUBOIUNDS  >= collectBounds(o.AMFX);

  assert k.Ready();
  ReadyBounds4(k);
  assert k.AMFO > o.AMFO;
  assert k.AMFO > k.AMFX >= k.AMFB; //>= collectBounds(k.AMFX);

  assert k.AMFO > o.AMFO > o.AMFX >= o.AMFB; // >= collectBounds(o.AMFX);

}



lemma  {:isolate_assertions} ThereIsNoSpoon(part : Object, whole : Object)
 //parts owner and bound are inside their whole's owner and bound..,
  requires part.Ready()
  requires whole.Ready()
  requires inside(part, whole)

  ensures part.AMFO >= whole.AMFO //ist just inside
  ensures bounds4(part)
  ensures bounds4(whole)

  // part.AMFB >= whole.AMFB //is soem thign else (boundsInsideBounds)
  {}

//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL
//EVIL EVIL EVIL EVIL

// method {:isolate_assertions} {:timeLimit 30}    Xlone_Clone_Clone(a : Object, m' : Klon)
//   returns (b : Object, m : Klon)
//   //this is pretty close to a "shallow clone" - acutally a "strucural clone" -
//   //clowning all owners etc but leaving the fields all empty
//   //we're solely called from Xlone_Via_Map  (and could be reintergrated, who knows?)
//     decreases * //(m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, |a.fields.Keys|, 15
//
//   requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound) //should be in calid
//   requires a !in m'.m.Keys
//   requires inside(a, m'.o) //can c == m'.o
//
// //START FROM XVM
//   requires m'.SuperCalidFragilistic()
//   requires m'.apoCalidse()
//   requires COKA: COK(a, m'.oHeap) ///includews a.Context(m'.oHeap)
//
//   requires a !in m'.m.Keys
// //  requires m'.ownersInKlown(a)  //luxon
// //  requires (klonCanKV(m',a,a))
//   requires (m'.c_amfx >= flatten(m'.clbound) >= flatten(m'.o.bound))
//   requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound) //should be in cali
//
//   requires a.Ready() && a.Valid()
//   // requires m'.ownersInKlown(a)
//   // requires m'.CalidCanKey(a)
//   requires (a  in m'.oHeap)  //willis
//   requires (a !in m'.m.Keys) //willis
//
// //END FROM XVM
//
// //FIELD MODEs-ISM HACK -- shouod go into calid or at laets supercalid!
//   requires forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes
//    ensures forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes
//   ensures unchanged( m.oHeap`fieldModes, m.m.Values`fieldModes )
//
// ///FUCK-prog
//     ensures m.SuperCalidFragilistic()
//     ensures a in m.m.Keys
//     ensures m.objectInKlown(a)
//     ensures m.m[a] == b
//     ensures a.fieldModes  == b.fieldModes
// //    ensures a.fields.Keys == b.fields.Keys
// //     or istKlonAlleFelder(a,b,m)... or somethinbg.
//       //this one is tricky
//       //the code *will* clone all objects fields eventually.
//       //BUT this may only hold at the very very end!
//       //consider a "pivot" object { fa == .. lots and lots of stuff, every object which points back to the root;  fb == 42. }
//       //if you copy fa and fb in alphabetical order, the EVERY recursive call finds we've started copying the root
//       //will finish *without* filling in all the fields...  knowing they'lll be done later.
//       //whichever method actually guarantees theyll be done later should do soethign abotu this.
//       //could track this with an extra ghost field n the Klon.  or, I dunno. something??
//
//     ensures b.Ready() && b.Valid()
//     ensures b.Context(m.hns())
//     ensures m.from(m')
// {
//   assert inside(a, m'.o);
//   ThereIsNoSpoon(a,m'.o);
//   assert a.AMFB >= m'.o.AMFB;
//   assert forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes;
//
//
//
//   assert (a.AMFB >= collectBounds(a.AMFX));
//
//   print "CALL Clone_Clone_CLone of:", fmtobj(a), " owned by ", fmtown(a.owner) ,"\n";
// //  print "VARIANT CCC ", |(m'.oHeap - m'.m.Keys)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";
//   print "VARIANT CCC ", |(m'.oHeap - m'.m.Keys +  {a})|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";
//
//   print "Clone_Clone_Clone ", fmtobj(a), " calling CAO ", fmtown(a.owner) ,"\n";
//   printmapping(m'.m);
//
// XCC_decreases_to_XAO(m',a);
//
// /////////////////////////////////////////////////////////////////////////////////
//   var rm := /*FAKE_*/Xlone_All_Owners(a, m');
// /////////////////////////////////////////////////////////////////////////////////
//
// assert forall z <- rm.m.Keys :: z.fieldModes == rm.m[z].fieldModes;
//
// //let's not do this again here!  //why not,  we have to!
//   if (a in rm.m.Keys) {
//
//     m := rm;
//     b := m.m[a]; //HMMmgv
//
//   assert a.fieldModes  == b.fieldModes;
//   ///axxume a.fields.Keys == b.fields.Keys;   ///FUCK AXXUME AXXUME AXXUME AXXUME FUCK DUCK KLUCK
//   ///see above comments.  we can't axxume thsi here cos it may not be true!
//
//     print "RETN Clone_Clone_CLone ", fmtobj(a), " already cloned: abandoning ship!!\n";
//     return;
//   } // a in rm.m.Keys - i.e.   done while cloning owners
// ////////////////////////////////////////////////////////////////////////////////
//
// assert rm.ownersInKlown(a);  //luxon
//
// /// From here, we are committed to calling "make"
//
//
//   assert (a.AMFB >= collectBounds(a.AMFX));
//   assert (rm.o.AMFB >= collectBounds(rm.o.AMFX));
//   assert (a.AMFB >= collectBounds(a.AMFX) >= rm.o.AMFB);
//   assert (a.AMFB >= collectBounds(a.AMFX) >= rm.o.AMFB  >= collectBounds(rm.o.AMFX));
//
//   assert  (rm.o.AMFO > rm.o.AMFX >= rm.o.AMFB  >= collectBounds(rm.o.AMFX));
//
//         //THIS ONE. THE lAST ONE5
//         //    &&  (AMFB >= collectBounds(AMFX))   //THIS ONE. THE lAST ONE
//         //THIS ONE. THE lAST ONE
//         // BOUNDNEST
//
//   OwnershipOfCloneGEQ(a.AMFB,collectBounds(a.AMFX),rm);
//
//   OwnershipOfCloneGEQ(a.AMFX,a.AMFB,rm);
//
//   assert computeOwnerForClone(a.AMFB, rm) >= computeOwnerForClone(collectBounds(a.AMFX), rm);
//
//   assert computeOwnerForClone(a.AMFX, rm) >= computeOwnerForClone(collectBounds(a.AMFB), rm);
//
//   assert a.AMFO >= a.AMFB;
//   assert a.AMFB >= rm.o.AMFB;
//   assert flatten(a.owner) >= flatten(a.bound);
//
//   var rowner := computeOwnerForClone(a.owner, rm); ///dunno when I wrote it but...
//   var rbound := computeOwnerForClone(a.bound, rm);
//
// //   var rowner := (set o <- a.owner :: rm.m[o]);   //12 July 2025
// //   var rbound := (set o <- a.bound :: rm.m[o]);
//
// //FUCK FUCK FUCK FUYCK FUCK // walkUpOwners(a.owner, rowner, a.bound, rm);
//
//   var r_AMFX := flatten(rowner);
//   var r_AMFB := flatten(rbound);
//
// ///FlattenGEQ(a.owner,a.bound);  doeesn't do what we wabnt:   flat(owner)>flat(bound) unrelat4ed to owner>bound!!
// MapThruKlonGEQ( flatten(a.owner), flatten(a.bound), rm);
//   assert a.AMFB >= rm.o.AMFB;
//   axxume r_AMFX >= r_AMFB;  //DUCK DUCK DUCK DUCK DUCK  //axxume***
//   assert r_AMFB >= rm.m[rm.o].AMFB >= rm.o.AMFB;  //newd collectO3wners somewhere...
//
// //   OwnershipOfCloneGEQ(a.owner,a.bound,rm);
// //   assert rowner >= rbound;
// //  FlattenGEQ(rowner, rbound);  //DUCK DUCK DUCK DUCK DUCK
//   //FIX THIS AND THE REST WILL FOLLOW???
//   // It's okay, I know nothing's wrong, nothing
//
//
// //   //is this good or is it jus5t dodgy?
// //   if (flerb(rbound, rm.clbound))
// //     { assert flerb(rbound, rm.clbound); }
// //     else
// //     { assert not(flerb(rbound, rm.clbound));
// //       assert flerb(rbound, rm.clbound);
// //       rbound := rm.clbound;
// //       assert flerb(rbound, rm.clbound);
// //       assert flerb(rbound, rm.clbound);
// //         }
// //   //is this dodgy or is it jus5t good?
// //
// // assert ( flerb(rbound, rm.clbound)) ; //is this wot we wont
// //
// // assert (flatten(rbound) >= flatten(rm.clbound));
//
//
//
//
//
//   print "Clone_Clone_CLone ", fmtobj(a), " have rowner ", fmtown(rowner) ," self not yet cloned\n";
//
// var rrm := rm; //prog THIS IS EVIL, should clean up and get rid of rrm completel6.
//
// assert forall z <- rrm.m.Keys :: z.fieldModes == rrm.m[z].fieldModes;
//
//
// print "Clone_Clone_Clone ", fmtobj(a), " boodle boodle boodle\n";
//
// //consider refactoring from here, so that make()
// // and then Xlone_All_Fields are called from a separate method
// // (whcih has all the owners being in Klon as a precondition)
// // this means after the conclusion of that method we could provide the new object has all fields.
// // we could ecen have another slot in the klon that tracks "half-baked" objects
// // (i.e. all owners cloned, but fields not yet done)
// // and then Xlone_Clone_CLone could call that method instead of make() directly.
//
// // much o the following pure copilot-generated, because...`
// //
// // this would make it easier to ensure that at the end of Xlone_Via_Map
// // the new object has all fields cloned.
// // (which it should do, really, since it's the only public entry point)
// // but it would be a bit more complicated.
// // on the other hand, it might be overkill.
// // dunno.  could be worth it.
// // could even be worth it to have a separate method for Xlone_All_Fields
// // (which it already is, but could be made more general, so that it could be
// // called from other places, not just Xlone_Clone_Clone)
// // (e.g. if we wanted to clone an object and then later fill in its fields
// // (perhaps in a different klon, or after some other operations)
// // (though not sure why we would want to do that, but who knows?))
// // could be worth it for clarity and modularity.
//
// var context := rrm.hns();
//
// print "CALLING MAKE...";
//
//
// assert rrm.preCalid();
// assert rrm.preCalid2();
// assert flatten(rrm.o.bound) == rrm.o.AMFB;
// assert flatten(rrm.clbound) >= rrm.o.AMFB;
// assert (rrm.o.AMFB >= collectBounds(rrm.o.AMFX));
//
// //random bounding shit
// // assert flatten(rbound) >= a.AMFB; //THIS ONE BOUNDNEST
//
// assert a.AMFB >= rrm.o.AMFB;
//    //should only be copyhin stuff that's INSIDE.
//       //except that's not what this doese!
//   //aee stuff eaerlier - ThereIsNoSpoon…
//
//
// //precalid
// assert (flatten(rrm.clbound) >= rrm.o.AMFB);
// assert (rrm.c_amfx >= flatten(rrm.clbound) >= rrm.o.AMFB);
//
// //dunno.  from above hack?
// ///assert (flatten(rbound) >= flatten(a.bound));  //BOUNDNEST
//
// /////////////////////////////////////////////////////////
// //general preconditions assertions that might be useful.
//
//   assert rrm.SuperCalidFragilistic();
//      //NOT needed for make - nor should it be, becausr
//      //Calid only applies when in the middle of a Clone
//      //but make can be acled jut to bild stuf..
//
//
//   assert COK(a, rrm.oHeap);
//   assert a.Ready();
//   assert a.Context(rrm.oHeap);
// //  assert rrm.hns() >= flatten(rowner);  ??prog 12 July 2025 - why is this here?
//
// //  FlattenGEQ(rowner,rbound);
//   assert (flatten(rowner) >= flatten(rbound)); //DUCK DUCK DUCK DUCK DUCK
//
// /////////////////////////////////////////////////////////
// //preconditions for make()
// //   - revised here 4July 2025 after revision there earlier July
// {
//   var oo := rowner;
//   var mb := rbound;
//
// //  assert isFlat(context);
// //  assert context >= oo >= mb; //context >= (oo+mb) shoudl be OK// oo >= mb not
//   assert forall o <- oo :: o.Ready();
//
//
//   if (not(flatten(mb) >= collectBounds(flatten(oo))))
//      {
//       mb := collectBounds(flatten(oo));  //.presumablyl the copy has it's  moving the bounds moved down.
//       //ukm is that even possible???  DUCK DUCK DUCK DUCK DUCK
//      }
//
//   assert (flatten(mb) >= collectBounds(flatten(oo)));
//
//
// }
// //WHAT THE FUCK FUCK
//
// //assert  (flatten(mb) >= collectBounds(flatten(oo))); //BOUNDSNEST
//
//
// //    assert forall o <- flatten(oo) :: flatten(mb) >= o.AMFB;
//    //17 June 2025 prog thinks this iswrong & shoud be in CalidLineKV
//
//
//
// ///forall o <- oo, ooo <- o.AMFO :: context >= o.AMFO >= ooo.AMFO
// ///forall o <- oo, ooo <- o.AMFO :: context >= o.AMFO >= ooo.AMFO
// ///forall o <- oo, ooo <- o.AMFO :: context >= o.AMFO >= ooo.AMFO
// // forall o <- flatten(oo) :: flatten(mb) >= o.AMFB
//
// // assert flatten(rbound) >= a.AMFB;
//
// assert forall z <- rrm.m.Keys :: z.fieldModes == rrm.m[z].fieldModes;
//
//
// //this one SHOHJLD BEFUCKNIG OK EH??
// // assert flatten(rbound) >= a.AMFB; //THIS ONE //BOUNDNEST
//
// //assert flatten(rbound) >= mapThruKlon(a.AMFB, m); //THIS ONE //BOUNDNEST
// axxume flatten(rbound) >= a.AMFB;  //DUCK DUCK DUCK DUCK DUCK   //prog FEAR SATAN   //axxume***
// //BOUNDNEST
//
// assert flatten(rowner) >= flatten(rbound); //BOUNDNEST
//
// assert bounds4(a);
//
// //HERE
// //  assert isFlat(context);   ///umm. let's no, really...? since it doesn't want to track thru?
//   //DUCK DUCK DUCK DUCK DUCK
//
//
// //    requires isFlat(context)
//     assert context >= flatten(rowner);
//     assert flatten(rowner) >= flatten(rbound);
//     assert AllReady(rowner);
//     axxume flatten(rbound) >= collectBounds(flatten(rowner));    //  //axxume***
// //revised early July2025
// //tweaked 28 Jul 2025
// //split 9 Sep 2025
//
// //// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
// // /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
//   b := new Object.make(a.fieldModes, rowner, context, "clone of " + a.nick, rbound);
// print "BACK FROM MAKE with ",fmtobj(b),"\n";
// //// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
// // /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
//
//   assert a.fieldModes  == b.fieldModes;
//
// //assert b.AMFB >= mapThruKlon(a.AMFB, m); //THIS ONE //BOUNDNEST  //DUCK DUCK DUCK DUCK DUCK
// //
// // //except q:=b aren't in the Klon yet!!!A
// //
// //besidews the 7-9 July 2025 rule says
// //dont map flattened references though the klon
// //only map object IDs (or sets of them)
// //denoting actual objects.
// //
// //IF we have flattenGEQ(a,b) which is relat4ed to "inside"
// //THEN we should have flattenGEQ(mapTK(a,m), mapTK(b,m))
// //(Likewise flattenGE or whateer
// // but we shouldn've necessarily have (and don't need)
// // any more than that??? ??? ???
//
// assert b.bound == rbound;
// assert b.AMFB  == flatten(rbound);
//
// assert bounds4(b);
// assert (b.AMFB >= collectBounds(b.AMFX));
// assert b !in rrm.oHeap;
// assert b.AMFO >= b.AMFX >= b.AMFB;
//
// assert b.fieldModes == a.fieldModes;
//
//
// //AHH FUCK THIS  OEN SH)UDI BE IMPORTNAT
// //assert b.AMFB >= a.AMFB;  //THIS ONE
// //THIS ONE
// //THIS ONE
// //THIS ONE
// //note we get this w few lines further down!
// //////////////////////////////////////////////////////////////////////
// //CALiDKV  preconditions
// //
// {
//   var k := a;
//   var v := b;
//
// assert v.AMFB >= k.AMFB;
//
// assert  (v.AMFO >= v.AMFB >= k.AMFB >= rrm.o.AMFB) ;
//
//  //THIS ONE
// assert  (v.AMFO >= v.AMFB >= collectBounds(v.AMFX));
// // assert  collectBounds(v.AMFX) >= k.AMFB;
// assert  v.AMFB >= k.AMFB;
// assert  k.AMFB >= rrm.o.AMFB;
//
// assert forall z <- rrm.m.Keys :: z.fieldModes == rrm.m[z].fieldModes;
//
//   assert a.fieldModes  == b.fieldModes;
//
//     assert k in rrm.oHeap;
//     assert rrm.SuperCalidFragilistic();
//     assert k.Ready() && k.Valid();
//     assert rrm.ownersInKlown(k);
//     assert rrm.o.Ready() && rrm.o.Valid();
//     assert rrm.objectInKlown(rrm.o);
//     assert k !in rrm.m.Keys;
//     assert v !in rrm.m.Values;
//     assert rrm.CalidCanKey(k);
//     assert NOV: v !in rrm.m.Values;
//     assert k in rrm.oHeap;
//     assert (v.Ready() && v.Valid() && v.Context(rrm.hns({v})));
//     assert rrm.m.Keys <= rrm.oHeap;
//     assert klonVMapOK(rrm.m);
//     assert canVMapKV(rrm.m, k, v);
//     assert v != k;
//     assert v !in rrm.oHeap;
//     assert (if (v==k) then (v in rrm.oHeap) else (v !in rrm.oHeap));
//     assert v.fieldModes == k.fieldModes;
//     assert k.Ready() && k.Valid() && k.Context(rrm.oHeap);
//     assert v.Ready() && v.Valid() && v.Context(rrm.hns({v}));
//     assert rrm.ownersInKlown(k);
// //    assert (v.AMFB >= k.AMFB); //17 June 2025 prog thinks this iswrong & shoud be in CalidLineKV
//     assert klonCanKV(rrm, k, v);
//     assert k.owner <= rrm.m.Keys <= rrm.oHeap;
//     assert rrm.m.Values <= rrm.hns();
//     assert rrm.HeapOwnersReady();
//     assert rrm.c_amfx <= rrm.oHeap;
// //    assert rrm.CalidLineKV(k,v);
//
//   assert a.fieldModes  == b.fieldModes;
//
// //CalidLineKV preconditions
//     assert k.Ready();
//     assert rrm.ownersInKlown(k);
//     assert v.Ready();
//     assert k.owner <= rrm.m.Keys <= rrm.oHeap;
//     assert rrm.m.Values <= rrm.hns();
//     assert rrm.o.Ready();
//     assert rrm.objectInKlown(rrm.o);
//     assert rrm.HeapOwnersReady();
//     assert rrm.c_amfx <= rrm.oHeap;
//
// //CalidLineKV body
//     assert (not(inside(k,rrm.o)) ==> (v == k));
//     assert (   (inside(k,rrm.o)) ==> (v !in rrm.oHeap));
// //    assert (   (inside(k,rrm.o)) ==> (v.AMFO >= v.AMFB >= k.AMFB >= rrm.o.AMFB)); //DUCK DUCK DUCK DUCK DUCK
//     assert (   (inside(k,rrm.o)) ==> (v.AMFO  >= v.AMFB  >= k.AMFB  >= rrm.o.AMFB)  );
// //    assert (   (inside(k,rrm.o)) ==> (v.owner >= v.bound >= k.bound >= rrm.o.bound) );  //THIS ONE //BOUNDNEST //DUCK DUCK DUCK DUCK DUCK
//
//
//     assert ( (v.AMFO  >= v.AMFB  >= k.AMFB)  );
// //    assert ( (v.owner >= v.bound >= k.bound) );//THIS ONE //BOUNDNEST
//
//
//     assert (k.AMFX <= rrm.m.Keys);
//     assert (k.AMFB <= rrm.m.Keys);
// //    assert (k.bound <= k.owner <= rrm.m.Keys);  //backasswards
//     assert (rrm.ownersInKlown(k));
//     assert (checkOwnershipOfClone(k,v,rrm));
//     assert (checkBoundOfClone(k,v,rrm));
//
//     assert rrm.CalidLineKV(k,v);
//
//     assert rrm.CKV_preconditions(k,v);
// }
//
// // assert (var m := rrm;
// //   if (outside(k, m.o))
// //     then (k == v)
// //     else if (k == m.o)
// //       then (v == m.m[m.o])
// //       else (
// //             && (v.owner == computeOwnerForClone(k.owner, m))))
// //             ;
// //
// //     assert rrm.CalidLineKV(k,v);
//
//
// assert forall z <- rrm.m.Keys :: z.fieldModes == rrm.m[z].fieldModes;
//   assert a.fieldModes  == b.fieldModes;
// //////////////////////////////////////////////////////////////////////
//   var xm := rrm.CalidKV(a,b);
// //////////////////////////////////////////////////////////////////////
//   assert a.fieldModes  == b.fieldModes;
// FieldModesAreStillOK(a,b,xm,rrm);
// assert forall z <- xm.m.Keys :: z.fieldModes == xm.m[z].fieldModes;
//
//   assert xm.from(rrm);
//
//   print "Clone_Clone_Clone map updated ", fmtobj(a), ":=", fmtobj(b) ,"\n";
//
// assert a in xm.m.Keys;
// assert b in xm.m.Values;
//
//   assert xm.m.Values >= m'.m.Values + {b};
//
//   XCC_decreases_to_XAF(a,b,xm);
//
// //////////////////////////////////////////////////////////////////////
// //////////////////////////////////////////////////////////////////////
//   m := /*FAKE_*/Xlone_All_Fields(a,b, xm); //this was deleted - who the fuck knows how long for?
// //////////////////////////////////////////////////////////////////////
// //////////////////////////////////////////////////////////////////////
//   assert a.fields.Keys == b.fields.Keys;
//
//
// assert forall z <- m.m.Keys :: z.fieldModes == m.m[z].fieldModes;
//
// assert m.from(xm);
// assert m.from(m');
//
//   print "RETN Clone_Clone_CLone of ", fmtobj(a), " retuning ", fmtobj(b) ,"\n";
//
//   assert m.m.Values >= m'.m.Values + {b};
//
// assert m.Calid();
//   assert a.fieldModes  == b.fieldModes;
//   assert a.fields.Keys == b.fields.Keys;
//
// }//end Clone_Clone_Clone
//







lemma /*VFF*/ XCC_decreases_to_XAO(m' : Klon, a : Object)
  // requires a !in m'.m.Keys
  // requires a  in m'.oHeap
  ensures  ((m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, |a.fields.Keys|, 15
        decreases to (m'.oHeap - m'.m.Keys), |a.AMFO|, |a.fields.Keys|, 12)
{
  // assert (15 decreases to 12);
  // assert (|a.fields.Keys|, 15 decreases to |a.fields.Keys|, 12);
  // assert (|a.AMFO|, |a.fields.Keys|, 15
  //   decreases to |a.AMFO|, |a.fields.Keys|, 12);
  // assert ((m'.oHeap - m'.m.Keys + {a}) >= (m'.oHeap - m'.m.Keys));
}




lemma /*VFF*/ XCC_decreases_to_XAF(a : Object, b : Object, m' : Klon)
  ensures  ((m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, |a.fields.Keys|, 15
        decreases to (m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, fielddiff(a,b), 10)
{}





//$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$
//$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$
//$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$




//{:timeLimit 30}
//yeat another earlier version now commented out
// method {:isolate_assertions} XClone_Clone_Clone(k : Object, m' : Klon) //commented out 29 FEB 2026
//   returns (v : Object, m : Klon)
//   //this is pretty close to a "shallow clone" - acutally a "strucural clone" -
//   //clowning all owners etc but leaving the fields all empty
//   //we're solely called from Xlone_Via_Map  (and could be reintergrated, who knows?)
//     decreases * //(m'.oHeap - m'.m.Keys + {k}), |k.AMFO|, |k.fields.Keys|, 15
//
//   requires m'.oHeap >= flatten(m'.clbound) >= flatten(m'.o.bound) //should be in calid
//   requires k !in m'.m.Keys
//   requires strictlyInside(k, m'.o) //can c == m'.o  -- NO!!!
//
// //START FROM XVM
//   requires m'.SuperCalidFragilistic()
//   requires m'.apoCalidse()
//   requires COKA: COK(k, m'.oHeap) ///includews k.Context(m'.oHeap)
//   requires HighCalidFragilistic(m')     requires HCF: HighCalidFragilistic(m')
//
//   requires k !in m'.m.Keys
// //  requires m'.ownersInKlown(k)  //luxon ///hmm why not?
//   requires (m'.c_amfx >= flatten(m'.clbound) >= flatten(m'.o.bound)) //should be in calid
//   requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound) //should be in calid
//
//   requires k.Ready() && k.Valid()
//   requires (k  in m'.oHeap)  //willis
//   requires (k !in m'.m.Keys) //willis
// //END FROM XVM
//
// //FIELD MODEs-ISM HACK -- shouod go into calid or at laets supercalid!
//   requires forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes
// //
//
// //THURSDAY NO ENSURES - 29 FEB 2026
// // //FUCKTODO
// //    ensures forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes
// //    ensures unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes )
// //
// // ///FUCK-prog
// //     ensures m.SuperCalidFragilistic()
// //     ensures HighCalidFragilistic(m)
// //
// //     ensures m.from(m')
// //     ensures m.objectInKlown(k)
// //     ensures m.m[k] == v
// //     ensures k.fieldModes  == v.fieldModes   //hmm shouldbe some kind of map.  mapping modes?
// //     ensures v.Ready() && v.Valid()
// //     ensures v.Context(m.hns())
// //     ensures m.CalidLineKV(k,v)   //JDVANCE
// //     ensures HighLineKV(k,v,m)       //TUESDAY
//
// //FUCKTODO
// //    ensures v.fields.Keys == k.fields.Keys ....   //KEYS
// //     or istKlonAlleFelder(k,v,m)... or somethinbg.
//       //this one is tricky
//       //the code *will* clone all objects fields eventually.
//       //BUT this may only hold at the very very end!
//       //consider k "pivot" object { fa == .. lots and lots of stuff, every object which points back to the root;  fb == 42. }
//       //if you copy fa and fb in alphabetical order, the EVERY recursive call finds we've started copying the root
//       //will finish *without* filling in all the fields...  knowing they'lll be done later.
//       //whichever method actually guarantees theyll be done later should do soethign abotu this.
//       //could track this with an extra ghost field n the Klon.  or, I dunno. something??
// {
//   assert HighCalidFragilistic(m');
//   assert forall k <- m'.m.Keys :: HighLineKV(k, m'.m[k], m');
//   assert FUCK: forall k <- m'.m.Keys :: HighLineKV(k, m'.m[k], m');
//
//  assert forall k <- m'.m.Keys :: HighLineKV(k, m'.m[k], m');
//
//   //FUCKTODO
//   assert COK(k, m'.oHeap) by { reveal COKA; }
//   // assert inside(k, m'.o);
//   // ThereIsNoSpoon(k,m'.o);
//   // assert k.AMFB >= m'.o.AMFB;
//   // assert forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes;
//   // assert unchanged(m'.oHeap`fieldModes, m'.m.Values`fieldModes );
//   //FUCKTODO
//
// //  assert (k.AMFB >= collectBounds(k.AMFX));
// assert nuBoundsOK(k.owner, k.bound);
//
//  assert forall k <- m'.m.Keys :: HighLineKV(k, m'.m[k], m');
//
//
//   print "CALL Clone_Clone_CLone of:", fmtobj(k), " owned by ", fmtown(k.owner) ,"\n";
// //  print "VARIANT CCC ", |(m'.oHeap - m'.m.Keys)|, " ", |k.AMFO|, " ", |(k.fields.Keys)|, " ", 15, "\n";
//   print "VARIANT CCC ", |(m'.oHeap - m'.m.Keys +  {k})|, " ", |k.AMFO|, " ", |(k.fields.Keys)|, " ", 15, "\n";
//
//   print "Clone_Clone_Clone ", fmtobj(k), " calling CAO", fmtown(k.owner) ,"\n";
//   printmapping(m'.m);
//
//    assert forall k <- m'.m.Keys :: HighLineKV(k, m'.m[k], m');
//
//   XCC_decreases to (m'.oHeap - m'.m.Keys), |a.AMFO|, |a.fields.Keys|, 12)(m',k);
//
// ///////////////////////////////////////////////////////////////////////// ////////
//   var rm := /*FAKE_*/Xlone_All_Owners(k, m')
//      by { reveal COKA; assert COK(k, m'.oHeap);
//           reveal FUCK; assert forall k <- m'.m.Keys :: HighLineKV(k, m'.m[k], m');
//           reveal HCF;  assert HighCalidFragilistic(m');
//   }
// //////////////////////////////////////////////////////////////ttv
//
//   if (k in rm.m.Keys) {
//
//     m := rm;
//     v := m.m[k]; //HMMmgv
//         assert unchanged(m'.oHeap`fieldModes, m'.m.Values`fieldModes );
//
//         assert COK(k, m'.oHeap);  assert COK(k, rm.oHeap);  assert COK(k, m.oHeap);
//
//         print "RETN Clone_Clone_CLone ", fmtobj(k), " already cloned: abandoning ship!!\n";
//
//         assert m'.SuperCalidFragilistic();  assert rm.SuperCalidFragilistic();
//         assert  m.SuperCalidFragilistic();
//
//         assert m.AllLinesCalid();
//         assert m.CalidLineKV(k,v);
//         assert HighLineKV(k,v,m);
//         assert HighCalidFragilistic(m);
//
//         return;
//   } // k in rm.m.Keys - i.e.   done while cloning owners
//
// v := k;  m := m';
//
// ////////////////////////////////////////////////////////////////////////////////
// /// From here, we are committed to calling "make"
//
//
//
//   //FUCKTODO
//   //
//   //   assert (k.AMFB >= collectBounds(k.AMFX));
//   //   assert (rm.o.AMFB >= collectBounds(rm.o.AMFX));
//   //   assert (k.AMFB >= collectBounds(k.AMFX) >= rm.o.AMFB);
//   //   assert (k.AMFB >= collectBounds(k.AMFX) >= rm.o.AMFB  >= collectBounds(rm.o.AMFX));
//   //
//   //   assert  (rm.o.AMFO > rm.o.AMFX >= rm.o.AMFB  >= collectBounds(rm.o.AMFX));
//   //
//   //         //THIS ONE. THE lAST ONE5
//   //         //    &&  (AMFB >= collectBounds(AMFX))   //THIS ONE. THE lAST ONE
//   //         //THIS ONE. THE lAST ONE
//   //         // BOUNDNEST
//   //
//   //   OwnershipOfCloneGEQ(k.AMFB,collectBounds(k.AMFX),rm);
//   //
//   //   OwnershipOfCloneGEQ(k.AMFX,k.AMFB,rm);
//   //
//   //   assert computeOwnerForClone(k.AMFB, rm) >= computeOwnerForClone(collectBounds(k.AMFX), rm);
//   //
//   //   assert computeOwnerForClone(k.AMFX, rm) >= computeOwnerForClone(collectBounds(k.AMFB), rm);
//   //
//   //   assert k.AMFO >= k.AMFB;
//   //   assert k.AMFB >= rm.o.AMFB;
//   //   assert flatten(k.owner) >= flatten(k.bound);
//   //
//   //FUCKTODO
//
//
//  // FUCK FUCK FUCK  FUCK FUCK FUCK   FUCK FUCK
//  //
//  //
//  //  we CANNOT FUCKING RELY on the mwapping like thqat.
//  //  we can ONLY MAP OBJECTS --- NOT owners.
//  //
//  //  mapTHruKlon( x.AMFB )  DOESS NOT WORK and MUST NOT WORK
//  // rather what we havede to get is
//  //
//  //  given, p, w, mp, mw
//  //  strictlyInside(p,w    ie.. p.AMFO >= q.AMFO
//  //  p = part
//  //  w - whole
//  //  SUCH THAT
//  //       fp = flatten P
//  //       fw = flatten w
//  //       fp >= fw  (or use recInside or something)
//  //  mp = map(p)  set of obejcts - owners - to set of objects
//  //  mw = map(w) set of obejcts - owners - to set of objects
//  //  THEN
//  //    we want to show - flattening IN THE mirror world
//  //  fmp = flatten mp
//  //  fmw = flatten mw
//  //  fmp >= fmq
//  //
//  //
//  // NOTE THAT flatten(map(X)) != map(flatten(x))
//  //   EXCEPT if X == Y.  flatten(map(X)) == flatten(map(Y))   //should be easuyily doable
//  //
//  // CASES
//  //
//
//
//   assert rm.ownersInKlown(k);  //luxon
//
//   assert k.owner <= rm.m.Keys;
//   assert k.bound <= rm.m.Keys;
//   assert rm.m.Keys >= k.AMFX >= k.AMFB;
//   assert k.AMFX <= rm.m.Keys;
//
//   assert AllReady(rm.m.Keys);
//   assert rm.SuperCalidFragilistic();
//   OwnersFromCalid(rm);
//   assert rm.CalidOwners();
//   assert rm.HeapContextReady() && rm.ValuesContextReady();
//
//   assert k.AMFX >= k.AMFB;
//   assert flatten(k.owner) >= flatten(k.bound);
//   assert nuBoundsOK(k.owner, k.bound);
// //  assert k.AMFB >= collectBounds(k.AMFX);
//  // assert flatten(k.bound) >= collectBounds(flatten(k.owner));
//
//
//   k.ExtraReady();
//   var rowner := computeOwnerForClone(k.owner, rm); ///dunno when I wrote it but...
//   var rbound := computeOwnerForClone(k.bound, rm);
//   var context := rm.hns();
//
// assert mappingOWNRsThruKlownKV(k.owner, rowner, rm);
// assert mappingOWNRsThruKlownKV(k.bound, rbound, rm);
//
// assert context >= flatten(rbound);
// //assert flatten(rbound) >= collectBounds(flatten(rowner));///JDVANCE
// assert context >= flatten(rowner);
// //assert flatten(rowner) >= flatten(rbound);   ///JDVANCE
//
// assert rowner <= rm.hns();  //note that context is just hns.
// assert rbound <= rm.hns();
//
//   var r_AMFX := flatten(rowner);
//   var r_AMFB := flatten(rbound);
//
//   assert nuBoundsOK(rowner, rbound);
//
//    if (k.owner == k.bound) {
//        assert rowner == rbound;
//        FlattenEq2(rowner, rbound);
//        assert r_AMFX == r_AMFB;
//      } else {
//       assert k.Ready();
//
//
//
//
//
//   opaque {
//     var  p := k.AMFX;
//     var  w := k.AMFB;
//     var mp := r_AMFX;
//     var mw := r_AMFB;
//     var  m := rm;
//
//           assert AllReady(p);
//           assert AllReady(w);
//           assert p >= w;
//           assert m.apoCalidse();
//           assert m.CalidOwners();
//           assert m.HeapOwnersReady();
//           assert m.ValuesOwnersReady();
//           assert p  <= m.m.Keys;
//           assert w  <= m.m.Keys;
//             // assert mappingOWNRsThruKlownKV(p,mp,m);
//             // assert mappingOWNRsThruKlownKV(w,mw,m);
//      }
//
//
//       HandInGlove(k.AMFX, k.AMFB, r_AMFX, r_AMFB, rm) by    //JDVANCE
//          {
//             var p, w, mp, mw, m := k.AMFX, k.AMFB, r_AMFX, r_AMFB, rm;
//             assert AllReady(p);
//             assert AllReady(w);
//             assert p >= w;
//             assert m.apoCalidse();
//             assert m.CalidOwners();
//             assert m.HeapOwnersReady();
//             assert m.ValuesOwnersReady();
//             assert p  <= m.m.Keys;
//             assert w  <= m.m.Keys;
//             //TRUMP assert mappingOWNRsThruKlownKV(p,mp,m);
//             //TRUMP assert mappingOWNRsThruKlownKV(w,mw,m);
//
//             // requires AllReady(mp)  // we can't be sure they'll all be ready…
//             // requires AllReady(mw)
//             // requires mp <= m.hns()  //29 Oct 2025
//             // requires mw <= m.hns()  //29 Oct 2025k
//             // requires mp <= m.m.Values
//             // requires mw <= m.m.Values
//
//             // requires p >  m.o.AMFO
//             // requires w >= m.o.AMFO
//
//
//
// //           assert k.AMFX <= rm.m.Keys;
// //           // assert r_AMFX <= m.hns();
// //           // assert r_AMFB <= m.hns();
// //           // assert rm.HeapContextReady() && rm.ValuesContextReady();
// //           // assert forall x <- m.hns() ::
// //           //    && ((x  in m.oHeap) ==> (rm.HeapContextReady()   && x.Ready()))
// //           //    && ((x !in m.oHeap) ==> (rm.ValuesContextReady() && (x in m.m.Values) && x.Ready()))
// //           //    && (x !in m.oHeap);
// //
// //           assert AllReady(r_AMFX);
// //           assert AllReady(r_AMFB);
//
//            }  //END by-proof for call of HandInGlobve
//       assert r_AMFX >= r_AMFB;
//      } //END case k.owner != k.bound
//
//
// assert (r_AMFX == r_AMFB) || (r_AMFX >= r_AMFB);
// assert (r_AMFX >= r_AMFB);
//
//
// assert rm.hns() >= r_AMFX >= r_AMFB;
//
// ///FlattenGEQ(k.owner,k.bound);  doeesn't do what we wabnt:   flat(owner)>flat(bound) unrelat4ed to owner>bound!!
// MapThruKlonGEQ( flatten(k.owner), flatten(k.bound), rm);
//   assert k.AMFB >= rm.o.AMFB;
//   assert r_AMFX >= r_AMFB;  //DUCK DUCK DUCK DUCK DUCK
//   assert r_AMFB >= rm.m[rm.o].AMFB >= rm.o.AMFB;  //newd collectO3wners somewhere...
//
// //   OwnershipOfCloneGEQ(k.owner,k.bound,rm);
// //   assert rowner >= rbound;
// //  FlattenGEQ(rowner, rbound);  //DUCK DUCK DUCK DUCK DUCK
//   //FIX THIS AND THE REST WILL FOLLOW???
//   // It's okay, I know nothing's wrong, nothing
//
//
// //   //is this good or is it jus5t dodgy?
// //   if (flerb(rbound, rm.clbound))
// //     { assert flerb(rbound, rm.clbound); }
// //     else
// //     { assert not(flerb(rbound, rm.clbound));
// //       assert flerb(rbound, rm.clbound);
// //       rbound := rm.clbound;
// //       assert flerb(rbound, rm.clbound);
// //       assert flerb(rbound, rm.clbound);
// //         }
// //   //is this dodgy or is it jus5t good?
// //
// // assert ( flerb(rbound, rm.clbound)) ; //is this wot we wont
// //
// // assert (flatten(rbound) >= flatten(rm.clbound));
//
//
//
//
//
//   print "Clone_Clone_CLone ", fmtobj(k), " have rowner ", fmtown(rowner) ," self not yet cloned\n";
//
//   //FUCKTODO
//   // assert forall z <- rm.m.Keys :: z.fieldModes == rm.m[z].fieldModes;
//   // assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
//   //FUCKTODO
//
// print "Clone_Clone_Clone ", fmtobj(k), " boodle boodle boodle\n";
//
// //consider refactoring from here, so that make()
// // and then Xlone_All_Fields are called from k separate method
// // (whcih has all the owners being in Klon as k precondition)
// // this means after the conclusion of that method we could provide the new object has all fields.
// // we could ecen have another slot in the klon that tracks "half-baked" objects
// // (i.e. all owners cloned, but fields not yet done)
// // and then Xlone_Clone_CLone could call that method instead of make() directly.
//
// // much o the following pure copilot-generated, because...`
// //
// // this would make it easier to ensure that at the end of Xlone_Via_Map
// // the new object has all fields cloned.
// // (which it should do, really, since it's the only public entry point)
// // but it would be k bit more complicated.
// // on the other hand, it might be overkill.
// // dunno.  could be worth it.
// // could even be worth it to have k separate method for Xlone_All_Fields
// // (which it already is, but could be made more general, so that it could be
// // called from other places, not just Xlone_Clone_Clone)
// // (e.g. if we wanted to clone an object and then later fill in its fields
// // (perhaps in k different klon, or after some other operations)
// // (though not sure why we would want to do that, but who knows?))
// // could be worth it for clarity and modularity.
//
// assert context == rm.hns();
//
// print "CALLING MAKE...";
//
// //FUCKTODO
// //
// //
// // assert rm.preCalid();
// // assert rm.preCalid2();
// // assert flatten(rm.o.bound) == rm.o.AMFB;
// // assert flatten(rm.clbound) >= rm.o.AMFB;
// // assert (rm.o.AMFB >= collectBounds(rm.o.AMFX));
// //
// // //random bounding shit
// // // assert flatten(rbound) >= k.AMFB; //THIS ONE BOUNDNEST
// //
// // assert k.AMFB >= rm.o.AMFB;
// //    //should only be copyhin stuff that's INSIDE.
// //       //except that's not what this doese!
// //   //aee stuff eaerlier - ThereIsNoSpoon…
// //
// //
// // //precalid
// // assert (flatten(rm.clbound) >= rm.o.AMFB);
// // assert (rm.c_amfx >= flatten(rm.clbound) >= rm.o.AMFB);
// //
// // //dunno.  from above hack?
// // ///assert (flatten(rbound) >= flatten(k.bound));  //BOUNDNEST
// //
// // /////////////////////////////////////////////////////////
// // //general preconditions assertions that might be useful.
// //
// //   assert rm.SuperCalidFragilistic();
// //      //NOT needed for make - nor should it be, becausr
// //      //Calid only applies when in the middle of k Clone
// //      //but make can be acled jut to bild stuf..
// //
// //
// //   assert COK(k, rm.oHeap);
// //   assert k.Ready();
// //   assert k.Context(rm.oHeap);
// // //  assert rm.hns() >= flatten(rowner);  ??prog 12 July 2025 - why is this here?
// //
// // //  FlattenGEQ(rowner,rbound);
//   assert (flatten(rowner) >= flatten(rbound)); //DUCK DUCK DUCK DUCK DUCK
//   //FUCKTODO
//
// /////////////////////////////////////////////////////////
// //preconditions for make()
// //   - revised here 4July 2025 after revision there earlier July
//
//
// //  assert isFlat(context);
// //  assert context >= oo >= mb; //context >= (oo+mb) shoudl be OK// oo >= mb not
//   assert forall o <- rowner :: o.Ready();
//
// //
// //   if (not(flatten(rbound) >= collectBounds(flatten(rowner))))
// //      {
// //       rbound := collectBounds(flatten(rowner));  //.presumablyl the copy has it's  moving the bounds moved down.
// //       //ukm is that even possible???  DUCK DUCK DUCK DUCK DUCK
// //      }
// //
// //
// //
// //   assert (flatten(rbound) >= collectBounds(flatten(rowner)));
//
//
//
// //WHAT THE FUCK FUCK
//
// //assert  (flatten(mb) >= collectBounds(flatten(oo))); //BOUNDSNEST
//
//
// //    assert forall o <- flatten(oo) :: flatten(mb) >= o.AMFB;
//    //17 June 2025 prog thinks this iswrong & shoud be in CalidLineKV
//
//
//
// ///forall o <- oo, ooo <- o.AMFO :: context >= o.AMFO >= ooo.AMFO
// ///forall o <- oo, ooo <- o.AMFO :: context >= o.AMFO >= ooo.AMFO
// ///forall o <- oo, ooo <- o.AMFO :: context >= o.AMFO >= ooo.AMFO
// // forall o <- flatten(oo) :: flatten(mb) >= o.AMFB
//
// // assert flatten(rbound) >= k.AMFB;
//
//   //FUCKTODO
//   // assert forall z <- rm.m.Keys :: z.fieldModes == rm.m[z].fieldModes;
//   // assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
//   //
//   // //this one SHOHJLD BEFUCKNIG OK EH??
//   // // assert flatten(rbound) >= k.AMFB; //THIS ONE //BOUNDNEST
//   //
//   // //assert flatten(rbound) >= mapThruKlon(k.AMFB, m); //THIS ONE //BOUNDNEST
//   // axxume flatten(rbound) >= k.AMFB;  //DUCK DUCK DUCK DUCK DUCK   //prog FEAR SATAN   //axxume***
//   // //BOUNDNEST
//   //
//   // assert flatten(rowner) >= flatten(rbound); //BOUNDNEST
//   //
//   // assert bounds4(k);
//   //
//   // //HERE
//   // //  assert isFlat(context);   ///umm. let's no, really...? since it doesn't want to track thru?
//   //   //DUCK DUCK DUCK DUCK DUCK
//   //
//   //
//   // //    requires isFlat(context)
//   //     assert context >= flatten(rowner);
//   //     assert flatten(rowner) >= flatten(rbound);
//   //     assert AllReady(rowner);
//   //     axxume flatten(rbound) >= collectBounds(flatten(rowner));    //  //axxume***
//   // //revised early July2025
//   // //tweaked 28 Jul 2025
//   // //split 9 Sep 2025
//   //FUCKTODO
//
// assert context >= flatten(rbound);  ///JDVANCE
// //assert flatten(rbound) >= collectBounds(flatten(rowner));
// assert context >= flatten(rowner);
// assert flatten(rowner) >= flatten(rbound);   ///JDVANCE
// //TRUMP assume context >= flatten(rowner) >= flatten(rbound);
//
// assert nuBoundsOK(rowner, rbound);
//
// //// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
// // /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
//   v := new Object.make(k.fieldModes, rowner, context, "clone of " + k.nick, rbound);
// print "BACK FROM MAKE with ",fmtobj(v),"\n";
// //// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
// // /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
//
//
// //JDVANCE
// assert strictlyInside(k, m'.o);
// assert strictlyInside(k, rm.o);
//
//
//     assert (k.Ready());
//     assert (rm.ownersInKlown(k));
//     assert (k in rm.oHeap);
//     assert (v.Ready());
//     assert (v in rm.hns({v}));
//     assert (v.AMFO  >= v.AMFB);
//     assert (v.AMFB >= k.AMFB);     ///JDVANCE
//     assert ( inside(k,rm.o) );
//     assert (   (inside(k,rm.o)) ==> (k.AMFB  >= rm.o.AMFB));
//     assert (not(inside(k,rm.o)) ==> (v == k));
//     assert (   (inside(k,rm.o)) ==> ((v !in rm.oHeap)) );
//     assert (mappingOwnersThruKlownKV(k,v,rm));     ///JDVANCE
//
//
//   assert ( inside(k,rm.o) );
//   assert (not(inside(k,rm.o)) ==> (3 == 2));
//
//   assert rm.OwnersLineKV(k,v);
//   assert  COK(k,  m'.oHeap);
//   assert  COK(k,  rm.oHeap);
//   assert  COK(k, rm.oHeap);
//
//
//   //FUCKTODO
//   // assert k.fieldModes  == v.fieldModes;
//   // assert unchanged( rm.oHeap`fieldModes, rm.m.Values`fieldModes );
//   //FUCKTODO
//
//
// //assert v.AMFB >= mapThruKlon(k.AMFB, m); //THIS ONE //BOUNDNEST  //DUCK DUCK DUCK DUCK DUCK
// //
// // //except q:=v aren't in the Klon yet!!!k
// //
// //besidews the 7-9 July 2025 rule says
// //dont map flattened references though the klon
// //only map object IDs (or sets of them)
// //denoting actual objects.
// //
// //IF we have flattenGEQ(k,v) which is relat4ed to "inside"
// //THEN we should have flattenGEQ(mapTK(k,m), mapTK(v,m))
// //(Likewise flattenGE or whateer
// // but we shouldn've necessarily have (and don't need)
// // any more than that??? ??? ???
//
//   //FUCKTODO
//   //   assert v.bound == rbound;
//   //   assert v.AMFB  == flatten(rbound);
//   //
//   //   assert bounds4(v);
//   //   assert (v.AMFB >= collectBounds(v.AMFX));
//   //   assert v !in rm.oHeap;
//   //   assert v.AMFO >= v.AMFX >= v.AMFB;
//   //
//   //   assert v.fieldModes == k.fieldModes;
//   //   assert unchanged( rm.oHeap`fieldModes, rm.m.Values`fieldModes );
//   //FUCKTODO
//
//
// //AHH FUCK THIS  OEN SH)UDI BE IMPORTNAT
// //assert v.AMFB >= k.AMFB;  //THIS ONE
// //THIS ONE
// //THIS ONE
// //THIS ONE
// //note we get this w few lines further down!
// //////////////////////////////////////////////////////////////////////
// //CALiDKV  preconditions
// //
//   //FUCKTODO
//     // {
//     // assert v.AMFB >= k.AMFB;
//     //
//     // assert  (v.AMFO >= v.AMFB >= k.AMFB >= rm.o.AMFB) ;
//     //
//     //  //THIS ONE
//     // assert  (v.AMFO >= v.AMFB >= collectBounds(v.AMFX));
//     // // assert  collectBounds(v.AMFX) >= k.AMFB;
//     // assert  v.AMFB >= k.AMFB;
//     // assert  k.AMFB >= rm.o.AMFB;
//     //
//     // assert forall z <- rm.m.Keys :: z.fieldModes == rm.m[z].fieldModes;
//     // assert unchanged( rm.oHeap`fieldModes, rm.m.Values`fieldModes );
//     //   assert k.fieldModes  == v.fieldModes;
//     //
//     //  CKV_preconditions
//         assert rm.SuperCalidFragilistic();
//         assert k.Ready() && k.Valid();
//         assert rm.ownersInKlown(k);
//         assert rm.o.Ready();
//          //&& rm.o.Valid();
//         assert rm.objectInKlown(rm.o);
//         assert k in rm.oHeap;   //CalisCanKey
//         assert k !in rm.m.Keys;
//         assert v !in rm.m.Values;
//         assert rm.CalidCanKey(k);
//         assert NOV: v !in rm.m.Values;
//         assert k in rm.oHeap;
//         assert (v.Ready() && v.Valid() && v.Context(rm.hns({v})));
//         assert rm.m.Keys <= rm.oHeap;
//         assert klonVMapOK(rm.m);
//         assert canVMapKV(rm.m, k, v); //klonCanKV
//         assert v != k;
//         assert v !in rm.oHeap;
//         assert (if (v==k) then (v in rm.oHeap) else (v !in rm.oHeap));
//         assert v.fieldModes == k.fieldModes;
// //        haventFuckedFieldModes(m', k, v, rm);  //needs to be AFTER CalidKV
//         assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
//         assert k.Ready() && k.Valid() && k.Context(rm.oHeap);
//         assert v.Ready() && v.Valid() && v.Context(rm.hns({v}));
//         assert rm.ownersInKlown(k);
//
//     //
//     // //    assert (v.AMFB >= k.AMFB); //17 June 2025 prog thinks this iswrong & shoud be in CalidLineKV
//     //     assert klonCanKV(rm, k, v);
//     //     assert k.owner <= rm.m.Keys <= rm.oHeap;
//     //     assert rm.m.Values <= rm.hns();
//     //     assert rm.HeapOwnersReady();
//     //     assert rm.c_amfx <= rm.oHeap;
//     // //    assert rm.CalidLineKV(k,v);
//     //
//     //   assert k.fieldModes  == v.fieldModes;
//     //
//     //CalidLineKV preconditions
//         assert k.Ready();
//         assert rm.ownersInKlown(k);
//         assert v.Ready();
//         assert k.owner <= rm.m.Keys <= rm.oHeap;
//         assert rm.m.Values <= rm.hns();
//         assert rm.o.Ready();
//         assert rm.objectInKlown(rm.o);
//         assert rm.HeapOwnersReady();
//         assert rm.c_amfx <= rm.oHeap;
//
//     //CalidLineKV body
//         assert (not(inside(k,rm.o)) ==> (v == k));
//         assert (   (inside(k,rm.o)) ==> (v !in rm.oHeap));
//     //    assert (   (inside(k,rm.o)) ==> (v.AMFO >= v.AMFB >= k.AMFB >= rm.o.AMFB)); //DUCK DUCK DUCK DUCK DUCK
// //TRUMP        assert (   (inside(k,rm.o)) ==> (v.AMFO  >= v.AMFB  >= k.AMFB  >= rm.o.AMFB)  );
//     //    assert (   (inside(k,rm.o)) ==> (v.owner >= v.bound >= k.bound >= rm.o.bound) );  //THIS ONE //BOUNDNEST //DUCK DUCK DUCK DUCK DUCK
//
//
//         assert ( (v.AMFO  >= v.AMFB  >= k.AMFB)  );
//     //    assert ( (v.owner >= v.bound >= k.bound) );//THIS ONE //BOUNDNEST
//
//
//         assert (k.AMFX <= rm.m.Keys);
//         assert (k.AMFB <= rm.m.Keys);
//     //    assert (k.bound <= k.owner <= rm.m.Keys);  //backasswards
//         assert (rm.ownersInKlown(k));
// //TRUMP        assert (checkOwnershipOfClone(k,v,rm));
//         assert (checkBoundOfClone(k,v,rm));
//
//
//         assert rm.OwnersLineKV(k,v);
//         assert rm.CKV_preconditions(k,v);
//         assert rm.CalidLineKV(k,v);
//     // }
//     //
//     // // assert (var m := rm;
//     // //   if (outside(k, m.o))
//     // //     then (k == v)
//     // //     else if (k == m.o)
//     // //       then (v == m.m[m.o])
//     // //       else (
//     // //             && (v.owner == computeOwnerForClone(k.owner, m))))
//     // //             ;
//     // //
//     // //     assert rm.CalidLineKV(k,v);
//     //
//     //
//     // assert forall z <- rm.m.Keys :: z.fieldModes == rm.m[z].fieldModes;
//     //   assert k.fieldModes  == v.fieldModes;
//     //   assert unchanged( rm.oHeap`fieldModes, rm.m.Values`fieldModes );
//
//   //FUCKTODO
//
//
//
//
//   assert  COK(k,  m'.oHeap);
//   assert  COK(k,  rm.oHeap);
//   assert  COK(k, rm.oHeap);
//
// /////////////////////////////////////////////////////////////// ///////
// assert rm.CKV_preconditions(k,v);
// //axxume rm.CKV_preconditions(k,v);
//   var xm := rm.CalidKV(k,v);
// //////////////////////////////////////////////////////////////////////
//   assert k.fieldModes  == v.fieldModes;
// haventFuckedFieldModes(rm,k,v,xm);
// FieldModesAreStillOK(k,v,xm,rm);
//
//
//   assert  COK(k,  m'.oHeap);
//   assert  COK(k, rm.oHeap);
//   assert  COK(k,  xm.oHeap);
//
//
//
//
//
//   //FUCKTODO
//   // assert forall z <- xm.m.Keys :: z.fieldModes == xm.m[z].fieldModes;
//   //   assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
//   //
//   //   assert xm.from(rm);
//   //
//   //   print "Clone_Clone_Clone map updated ", fmtobj(k), ":=", fmtobj(v) ,"\n";
//   //
//   // assert k in xm.m.Keys;
//   // assert v in xm.m.Values;
//   //
//   //   assert xm.m.Values >= m'.m.Values + {v};
//   //FUCKTODO
//
//   XCC_decreases_to_XAF(k,v,xm);
//
// //////////////////////////////////////////////////////////////////////
// //////////////////////////////////////////////////////////////////////
// assert COK(k, xm.oHeap);
//   m := /*FAKE_*/Xlone_All_Fields(k,v, xm); //this was deleted - who the fuck knows how long for?
// //////////////////////////////////////////////////////////////////////
// //////////////////////////////////////////////////////////////////////
// //KEYS  assert k.fields.Keys == v.fields.Keys;
//
//   assert  COK(k,  m'.oHeap);
//   assert  COK(k, rm.oHeap);
//   assert  COK(k,  xm.oHeap);
//   assert  COK(k,   m.oHeap);
//
//   assert HighLineKV(k,v,m);
//   assert m.CalidLineKV(k,v);
//
// // assert forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes;
// //   assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
//
//   //FUCKTODO
//   // assert m.from(xm);
//   // assert m.from(m');
//   //
//   //   print "RETN Clone_Clone_CLone of ", fmtobj(k), " retuning ", fmtobj(v) ,"\n";
//   //
//   //   assert m.m.Values >= m'.m.Values + {v};
//   //
//   // assert m.Calid();
//   //   assert k.fieldModes  == v.fieldModes;
//   // //KEYS  assert k.fields.Keys == v.fields.Keys;
//   //   assert unchanged( m.oHeap`fieldModes, m.m.Values`fieldModes );
//   //FUCKTODO
//
//
// }//end XClone_Clone_Clone
//




//$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$
//$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$
//$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$







lemma /*VFF*/ XAO_decreases_to_XVM(a : Object,  am : Klon, xo : Object, xm : Klon)

  requires a != xo

  requires a.AMFO > xo.AMFO
  requires xm.from(am)
  requires xo in (a.owner - xm.m.Keys)
  requires a in am.oHeap
  requires COK(a,am.oHeap)

  ensures  a in xm.oHeap
  ensures  xo in a.owner
  ensures  xo !in xm.m.Keys
  ensures  xo !in am.m.Keys

  ensures  xm.oHeap == am.oHeap
  ensures  xm.m.Keys >= am.m.Keys
  ensures  a in xm.oHeap

  ensures ((am.oHeap - am.m.Keys) nonincreases to (xm.oHeap - (xm.m.Keys + {xo})))
  ensures ((am.oHeap - am.m.Keys), |a.AMFO|, |a.fields.Keys|, 12
                 decreases to (xm.oHeap - (xm.m.Keys + {xo})), |xo.AMFO|, |xo.fields.Keys|, 10)
{
  reveal am.Calid();
  BiggerIsStrictlyBigger(a.AMFO, xo.AMFO);

  assert xm.from(am);
  assert xm.oHeap == am.oHeap;
}

//
//
// lemma /*VFF*/ XCC_decreases_to_XVM(m' : Klon, a : Object)
//   requires a !in m'.m.Keys
//   requires a  in m'.oHeap
//   // ensures ((m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, |a.fields.Keys|, 15
//   //       decreases to ((m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, |a.fields.Keys|, 20))
// {
//   assert (m'.oHeap - m'.m.Keys + {a}) > (m'.oHeap - m'.m.Keys + {a});
//
// }
//
//



////££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££
////££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££



lemma Set2NoDifferenceEq<T>(a : set<T>, b : set<T>)
 requires a >= b
 requires a  - b == {}
  ensures a == b
  {
    SetMinus0(a,b);
    // assert ( a >= b )       ==> (forall x <- b :: x in a);
    // assert ( a  - b == {} ) ==> (forall x <- a :: x in b);
    // assert ( a >= b ) && ( a  - b == {} );
    // assert (forall x <- b :: x in a) && (forall x <- a :: x in b);
    assert a == b;
  }


////££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££
////££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££


lemma /*VFF*/ XAF_decreases_to_XFM(a : Object, b : Object, m' : Klon)
  ensures (
    (m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, fielddiff(a,b), 10
    decreases to
    (m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, fielddiff(a,b), 5 //Xlone_Field_Map
  )
 {}

////££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££




///÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷
//. dead code culed from earlier version of XFM
//
//   //if (ofv in m.m.Keys)
//   {
//     ///HAW HAW HAW - should this be the OTHER WAY AROUND
//     ///i.e at this pint, if ofv IS NOT in m.m.Keys
//    ////then we clone it ///then after having done so
//     ///we do the actusl field update
//
//           rfv := m.m[ofv];
//       {
//       // KaTHUMP(b,n,rfv,m);
//
//       var source := a;
//       var clone  := b;
//       var t := ofv;
//       var u := rfv;
//
//       assert strictlyInside(source, m.o); ///axxume
//       assert source.Ready();
//       assert source.Valid();
//       assert clone.Ready();
//       assert t.Ready();
//       assert u.Ready();
//       assert m.ownersInKlown(t);
//       assert m.apoCalidse();
//       assert m.SuperCalidFragilistic(); ///axxume
//       assert m.objectInKlown(source);
//       assert clone == m.m[ source ];
//       assert n in source.fields.Keys;
//       assert t == source.fields[n];
//       assert n in clone.fields.Keys;
//       assert u == clone.fields[n];
//       assert t in m.m.Keys;
//       assert u == m.m[ t ];
//       assert clone != source;
//       assert outside(t, clone);
//
//       BirnamWood10(source, clone, n, t, u, m);
//       BirnamWood20(source, clone, n, t, u, m);
//       }
//
//
// //       //I think this is there to capture postconditions?
// //         //GRRRRRRRRRRRR GGGGGGGGGGGGGGGG
// //         //assert isStructuralClone(rfv,ofv);
// //           assert  a.fields.Keys == old(a.fields.Keys);
// //           assert  rfv.fields.Keys == ofv.fields.Keys;
// //           assert  rfv.fieldModes == ofv.fieldModes;
// //
// //           assert  m.from(m);
// //           assert  m.SuperCalidFragilistic();
// //           assert  m.ownersInKlown(a);
// //           assert  a in m.m.Keys;
// //           assert  n in a.fields.Keys;
// //           assert  n in b.fields.Keys;  //TODO9Sep
// //           assert  old(fielddiff(a,b)) decreases to fielddiff(a,b);
// //           assert  m.m[a] == b;
// //           assert  m.ownersInKlown(a.fields[n]);
// //           // assert  m.m[ a.fields[n] ] == b.fields[n];
// //           // assert  m.m[ a.fields[n] ] == m.m[a].fields[n];
// //           assert a.fieldModes.Keys == b.fieldModes.Keys;
//
//
//
//
//
//           BirnamWood10(a, b, n, ofv, rfv, m);
//
//           assert forall z <- m.m.Keys :: z.fieldModes == m.m[z].fieldModes;
//           assert ofv in m.m.Keys;
//           assert rfv.fieldModes == ofv.fieldModes;
//           assert RFVOFV: rfv.fieldModes == ofv.fieldModes;
//
//           assert b.Ready();
//           assert b.fields.Keys <= b.fieldModes.Keys;
//           assert n in b.fieldModes.Keys;
//           assert n !in b.fields.Keys;
//           assert refOK(b, rfv);   //TODO9Sep
//           assert modeOK(b, b.fieldModes[n], rfv);  //TODO9Sep
//
//           assert m.Calid();
//           assert m.SuperCalidFragilistic();
//           assert m.m[ofv] == rfv;
//           assert m.AllLinesCalid();
//           assert m.CalidLineKV(ofv,rfv);
//
//           assert m.HeapContextReady();
//           assert forall x <- m.oHeap :: (x.Ready() && x.Valid() && x.Context(m.oHeap));
//           assert ofv in m.oHeap;
//
//
//           assert forall z <- m.m.Keys :: z.fieldModes == m.m[z].fieldModes;
//           assert rfv.fieldModes == ofv.fieldModes;
//
//             //note, this doesn't have to be "a" couold be anything we've already (started) copying
//             print "RETN XFM: already copied, adding field, bailing out\n";
//             assert n !in b.fields.Keys;
//
//
//           assert m.Calid();
//           assert m.SuperCalidFragilistic();
//           assert m.m[ofv] == rfv;
//           assert m.AllLinesCalid();
//           assert m.CalidLineKV(ofv,rfv);
//
//             assert rfv == m.m[ofv];
//             assert  m.CalidLineKV(a,b);
//             assert  m.CalidLineKV(ofv,rfv);
//
//
//
//
//           assert rfv.fieldModes == ofv.fieldModes;
//           assert forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes;
//
//             assert m.SuperCalidFragilistic();
//             assert m .Calid();
//             assert m == m;
//             assert MCALID: m .Calid();
//             assert m .SuperCalidFragilistic();
//             assert SCFL2: m.SuperCalidFragilistic();
//             assert m .Calid();
//
//             assert a   in m.oHeap;
//             assert ofv in m.oHeap;
//             assert ofv.Context(m.hns());
//
//             assert  n in a.fields.Keys;
//             assert  n in old(a.fields.Keys);
//             assert  old(a.fields.Keys) == a.fields.Keys;
//             assert  n !in b.fields.Keys;
//             assert  old(b.fields.Keys) == b.fields.Keys;
//
//             assert b == m.m[a];
//             assert b in m.m.Values;
//             assert b in m.hns();
//             assert b.Context(m.hns());
//         assert  m.SuperCalidFragilistic() by { reveal SCFL2; }
//             //FIELD UPDARE HERE
//             assert b.Ready() && b.Valid() && b.Context(m.hns());
//
//             assert forall x <- m.m.Keys | x != b :: m.CalidLine(x);
//             var AFLDS := a.fields;
//             assert  n !in b.fields.Keys;
//             var OLDHAMFLDS := b.fields.Keys;
//
//   assert a.Ready();
//   assert a in m.m.Keys;
//   assert b.Ready();
//   assert m.SuperCalidFragilistic();
//   assert n  in a.fields.Keys;
//   assert ofv == a.fields[n];
//   assert n !in b.fields.Keys;
//   // assert a.fields.Values <= m.m.Keys;  //whaaat
//   //assert b.fields.Keys >= a.fields.Keys; //whaaat
//   assert rfv == m.m[ofv];
// //  BirnamWood2(a,b,n, ofv, rfv, m);
//   assert b.Ready() && b.Valid() && b.Context(m.hns());
//   label B4:
//
//
//
//   assert  n in b.fields.Keys;
//   assert b.fields.Keys == OLDHAMFLDS + {n};
//   assert b.fields.Keys == old@B4(b.fields.Keys) + {n};
//    assert a  in m.oHeap;
//    assert b !in m.oHeap;
//    assert a != b;
//         assert a.fields == old@B4(a.fields);
//               assert a.fields == AFLDS;
//               assert  old(a.fields.Keys) == a.fields.Keys;
//           //note b could equal  s rfv & if so, then this fucks with rfv :-(
//               assert  n in b.fields.Keys;
//               assert  n !in old(b.fields.Keys);
//               assert  b.fields.Keys == old@B4(b.fields.Keys) + {n};
//             assert b.Ready();
//     assert (b.fields.Keys <= b.fieldModes.Keys);  ///a //`TODO9`Sep
//     assert (forall n <- b.fields :: refOK(b, b.fields[n]));  ///b //TODO9Sep
//     assert (forall n <- b.fields :: modeOK(b, b.fieldModes[n], b.fields[n])); ///c //TODO9Sep
//             assert b.Valid();
//             assert b.Context(m.hns());//* q1 //TODO9Sep
//
//             assert  old(a.fields.Keys) == a.fields.Keys;
//             assert  (a.fields.Keys - b.fields.Keys) == (a.fields.Keys - (old(b.fields.Keys) + {n})); //TODO9Sep
//             assert  (a.fields.Keys - b.fields.Keys) <  (a.fields.Keys - (old(b.fields.Keys)));
//             assert  (a.fields.Keys - b.fields.Keys) < old(a.fields.Keys -      b.fields.Keys);
//           //  assert  (old(fielddiff(a,b)) decreases to fielddiff(a,b));
//
//             assert forall x <- m.m.Keys | x != b :: m.CalidLine(x); //TODO9Sep
//             assert  ofv in m.m.Keys;
//             assert  m.CalidLineKV(ofv,rfv);
//             assert  m.ownersInKlown(ofv);
//             assert  m.SuperCalidFragilistic() by { reveal SCFL; }
//
//             assert  m.from(m);
//             assert  a in m.m.Keys;
//             assert  n in a.fields.Keys;
//             assert  n in b.fields.Keys;
//
//             assert  m.m[a] == b;
//             assert  m.m[ a.fields[n] ] == b.fields[n];
//             assert  m.m[ a.fields[n] ] == m.m[a].fields[n];
//             assert  a.fieldModes.Keys == b.fieldModes.Keys;
//
//             assert rfv.fieldModes == ofv.fieldModes by { reveal RFVOFV; } //TODO9Sep
//             assert forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes; //TODO9Sep
//             // assert  m.SuperCalidFragilistic();
//             // assert  m == m;
//             assert  m .SuperCalidFragilistic() by { reveal SCFL; }
//             return;   ///÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷
//     } ///÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷÷
//
//
//
//
//
// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
// //progTODOFUCK
//   b.fields := b.fields[n:= rfv];
// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
//
//   assert  m.m[a] == b; //from requiremwnt on m
//
// //khjx Wed 3 Sept 2025 14:17
// //
// // ////////// isn't this all subssumed in the Xlone_Via_Map…
// // //
// // // // // //p-`0  // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
// // // // preoconditions for m.CalidKV(ofv,rfv)
// // //what the RUCK???  WHY WHY WHY??
// //
// // {// make a CalidCanKV or something
// //     var k := ofv;
// //     var v := rfv;
// //     var o := m.o;
// //     assert k.Ready() && k.Valid() by { reveal OFV; assert k.Ready() && k.Valid(); }
// //     assert m.ownersInKlown(k);
// //     assert o.Ready() && o.Valid();
// //     assert m.objectInKlown(o);
// // //  assert m.CalidCanKey(k); //willjis - NOO, put in by Xlone_VIa_Map...
// //     assert k !in m.m.Keys by { assert k == ofv; reveal OFV_NOTIN; assert k !in m.m.Keys;  }
// //     assert v !in m.m.Values;
// //     assert m.HeapContextReady();
// //     assert m.ValuesContextReady();
// //     assert m.Calid();
// //     assert k in m.oHeap;
// //     assert v in (m.hns({v}));
// //     assert (v.Ready() && v.Valid() && v.Context(m.hns({v})));
// //     assert m.m.Keys <= m.oHeap;
// // }
// //
// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
// //
// //
// // //progTODOFUCK //progTODOFUCK //progTODOFUCK
// //  m  := m.CalidKV(ofv,rfv);
// //
// // //progTODOFUCK //progTODOFUCK //progTODOFUCK
// //   assert  m.m[a] == b; //from requiremwnt on m
// //   assert  m.m[ a.fields[n] ] == b.fields[n];
// //   assert  m.m[ a.fields[n] ] == m.m[a].fields[n];
// // // //
// // // // //prog UNFINISHJED fucku fucky gfucky
// // // // //need to reesta lish Calid. oh FUCK.
// // // //   assert rfv.Ready() && rfv.Valid() && rfv.Context(m.hns({rfv}));
// // // //   assert b.Ready()   && b.Valid()   && b.Context(m.hns({rfv}));
// // // //   // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
// // // //
// print "RETN Clone_Field_Map: ", fmtobj(a), " pivot:", fmtobj(m.o), "\n";
//
//   assert  m.from(m);
//   assert  m.SuperCalidFragilistic();
//   assert  m.ownersInKlown(a);
//   assert  a in m.m.Keys;
//   assert  n in a.fields.Keys;
//   assert  n in b.fields.Keys;
//   assert  old(fielddiff(a,b)) decreases to fielddiff(a,b);
//   assert  m.m[a] == b;
//   assert  m.ownersInKlown(a.fields[n]);
//   // assert  m.m[ a.fields[n] ] == b.fields[n];
//   // assert  m.m[ a.fields[n] ] == m.m[a].fields[n];
//   assert a.fieldModes.Keys == b.fieldModes.Keys;
//
//
// } //end Clone: /_Field_Mapassert a in xm.m.Keys;
//






///spare code culled from an EVEN earlier version of XFM
//
//  requires m'.HeapContextReady() && m'.ValuesContextReady()
//  requires m'.Calid()
//  requires refOK(f,t)
//  requires f.Ready() && f.Valid()
//  requires t.Ready() && t.Ready()
//
//  // ensures |f.AMFO| >= |t.AMFO|
// {
// //t  assert (f==t) || refBI(f,t) || refDI(f,t);
// //
// // //castle "="
// //  assert (f==t) ==> (|f.AMFO| == |t.AMFO|);
// //
// // //castle RefBI
// //   assert (refBI(f,t)) ==> (f.AMFB >= t.AMFX);
// //   assert  t.AMFX+{t} == t.AMFO;
// //
//   assert  f.AMFO >= f.AMFX + {f};
//   assert  f.AMFO - {f} == f.AMFX;
//
//   // assert (refBI(f,t)) ==> |f.AMFO| >= |f.AMFB+{f}|;
//   //assert |f.AMFB+{f}| >= |t.AMFO-{t}|;
//
// //TO BNE FINISHED
//
// //castle ref DI
//  assert  (refDI(f,t)) ==>  (f.AMFO == t.AMFX);
// }

























method {:isolate_assertions} {:timeLimit 15} origKaTHUMP(a : Object, n : string, b : Object, m' : Klon)
  requires a.Valid()
  requires a.OwnersWithin(m'.hns({b}))
  /////////////////////////////////////////
  //requires a in m'.m.Values //note carefully, this.  except it's  //too much effort...re: I read your oopsla paper...
  /////////////////////////////////////////

  //requires n  in a.fieldModes.Keys //subsumed by FieldValidNV
  requires n !in a.fields

  requires m'.SuperCalidOwners()   //do we need this?  sure?
  requires m'.CalidOwners()
  requires a.AllFieldsValid()
  requires a.FieldValidNV(n, b)
//need to decide if origB -> B is in m.m.Keys or not
   ensures a.OwnersWithin(m'.hns({b}))
  // ensures a.Valid()
   ensures n  in a.fields.Keys
   ensures a.fields[n] == b
//NO_FIELDMODES    ensures a.fieldModes.Keys == old(a.fieldModes.Keys)
   ensures a.fields.Keys == old(a.fields.Keys) + {n}
   ensures a.fields == old(a.fields)[n := b]
    //ensures (forall z <- m'.m.Keys | z != a :: z.fields == old(z.fields))

    //too much effort...
  //  ensures (forall z <- m'.m.Values :: z.fields ==
  //              if (z == a) then (old(z.fields)[n := b])
  //                  else (old(z.fields)))

 //restoring CalidOwnwers requires either knowning what the orig-side objects are
 //or coming in with that already set up!
 //ensures m'.CalidOwners()
  modifies a`fields
{
  assert a.Valid();
  print "CALL KaTHUMP ", fmtobj(a), ".", n, " to ", fmtobj(b), "\n";
  a.fields := a.fields[n := b];
  print "RETN KaTHUMP done ", fmtobj(a), "\n";

  assert a.fields[n] == b;

 //too much effort...
  // assert (forall z <- m'.m.Values :: z.fields ==
  //              if (z == a) then (old(z.fields)[n := b])
  //                  else (old(z.fields)));

  assert a.FieldValidNV(n, b);
  assert a.AllFieldsValid();
  a.ValidMeansAllFieldsValid();
  assert a.Valid();
}


// method {:isolate_assertions} KaTHUMP(a : Object, n : string, b : Object, m' : Klon)
//   requires a.Valid()
//   requires n  in a.fieldModes.Keys
//   requires n !in a.fields.Keys
//   requires m'.SuperCalidFragilistic()
//    ensures a.Valid()
//    ensures n  in a.fields.Keys
//    ensures a.fields[n] == b
//    ensures a.fieldModes.Keys == old(a.fieldModes.Keys)
//    ensures a.fields.Keys == old(a.fields.Keys) + {n}
//    ensures a.fields == old(a.fields)[n := b]
//    ensures forall z <- m'.m.Keys | z != a :: z.fields == old(z.fields)
//    ensures (forall z <- m'.m.Keys :: z.fields ==
//        if (z == a) then (old(z.fields)[n := b])
//                    else (old(z.fields)))
//    ensures m'.SuperCalidFragilistic()
//   modifies a`fields
// {
//   print "CALL KaTHUMP ", fmtobj(a), ".", n, " to ", fmtobj(b), "\n";
//   a.fields := a.fields[n := b];
//   print "RETN KaTHUMP done ", fmtobj(a), "\n";
// }

lemma {:isolate_assertions} DownInSplendor(heapkeys: set<Object>, a : Object, o : Object)
  requires o  in heapkeys
  requires a !in heapkeys
  requires o != a
  ensures (heapkeys + {a}) > (heapkeys + {o})
  ensures (heapkeys + {a}) decreases to (heapkeys + {o})
  {}

lemma {:isolate_assertions} TieMeKangaDown(aa : set<string>, bb : set<string>, n : string)
  requires aa > bb
  requires n  in aa
  requires n !in bb
  ensures (aa - bb) > (aa - (bb + {n}))
  ensures (|aa - bb|) > (|aa - (bb + {n})|)
  ensures (aa - bb) decreases to (aa - (bb + {n}))
  ensures (|aa - bb|) decreases to (|aa - (bb + {n})|)
  {}


// //
// lemma /*VFF*/ {:timeLimit 5}  XFM_decreases_to_XVM(a : Object, b : Object, m' : Klon, ofv : Object, m: Klon)
//   requires refOK(a,ofv)
//   requires m'.Calid()
//   requires m.from(m')
//   requires a in m'.oHeap
//   requires COK(a,m'.oHeap)
//
//   requires m.from(m')
//   requires a in m'.oHeap
//   requires COK(a,m'.oHeap)
//
//   ensures  m.oHeap == m'.oHeap
//   ensures (
//     (m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, fielddiff(a,b), 5 //Xlone_Field_Map
//     decreases to
//     (m.oHeap - m.m.Keys + {ofv}), |ofv.AMFO|, |ofv.fields.Keys|, 20)
// {
// //  HERE.
// }

lemma AddExtraElement<T>(e : T, aa : set<T>, bb : set<T>)
  //if e !in aa, bb == aa + {e} ensures bb >= aa, |bb| >= |aa|
  requires e !in aa
  requires bb == aa + {e}
  ensures  bb  >= aa
  ensures |bb| >= |aa|
{}

lemma  RemoveAddContainedElement<T>(aa : set<T>, bb : set<T>, e : T)
  requires e in aa
  ensures  (aa - bb + {e}) == (aa - (bb - {e}))
{}

// lemma  RemoveAddExtraElement<T>(aa : set<T>, bb : set<T>, e : T)
//   requires e in aa
//   requires e !in bb
//   ensures  (aa - bb + {e}) == (aa - (bb - {e}))
// {
//   assert e in (aa - bb);
//
// }


//I think this was "ater" the official fall of tb4 walwaa


lemma /*VFF*/ XFM_decreases_to_XVM(a : Object, b : Object, ofv : Object, m' : Klon)

  requires m'.HeapContextReady() && m'.ValuesContextReady() &&  m'.Calid()
  requires m'.m.Keys <= m'.oHeap  //must be in Calid()?

  requires ofv  in m'.oHeap
  requires COK(ofv,m'.oHeap)
  requires ofv !in m'.m.Keys
  requires ofv != a

  requires AINH: a in m'.oHeap
  requires       a in m'.oHeap
  requires COKA: COK(a, m'.oHeap)
  requires       COK(a,m'.oHeap)
  requires AINK: a in m'.m.Keys
  requires       a in m'.m.Keys

//////////////LETS MAKE LURVE


  requires a.Ready() && a.Valid()

  //we're just called from Xlone_Via_Map  (and could be reintergrated, who knows?)
//  requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound)
  requires a in m'.m.Keys
  requires m'.objectInKlown(a)
//  requires inside(a, m'.o)    //deleted Nov 8 2025 - cos this can be called on
                                //outwide objects, eventuyally to share them not clone them?

  requires (m'.c_amfx >= flatten(m'.clbound) >= flatten(m'.o.bound))
//  requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound)

///////////////AND LISTEN DEATH FROM ABOVW

  ensures (
    (m'.oHeap - m'.m.Keys + {a}),   |a.AMFO|,    fielddiff(a,b), 5 //Xlone_Field_Map
    decreases to
    (m'.oHeap - m'.m.Keys + {ofv}), |ofv.AMFO|, |ofv.fields.Keys|, 20)
{

DownInSplendor(m'.oHeap - m'.m.Keys, a, ofv);


  assert (
    ((m'.oHeap - m'.m.Keys) + {a}),   |a.AMFO|,    fielddiff(a,b), 5 //Xlone_Field_Map
    decreases to
    ((m'.oHeap - m'.m.Keys) + {ofv}), |ofv.AMFO|, |ofv.fields.Keys|, 20);


assert (m'.oHeap - m'.m.Keys + {a},   |a.AMFO|,   fielddiff(a,b), 5 //Xlone_Field_Map
    decreases to
       m'.oHeap - m'.m.Keys + {ofv}, |ofv.AMFO|, |ofv.fields.Keys|, 20);
}

//   assert ofv  in m'.oHeap;
//   assert m'.m.Keys <= m'.oHeap;
//   assert (m'.oHeap - m'.m.Keys + {a} decreases to m'.oHeap - m'.m.Keys  + {ofv});
//
//   assert a  in  m'.m.Keys by { reveal AINK; }
//   assert a  in m'.oHeap by { reveal AINH; }
//
//   assert a  in (m'.oHeap - m'.m.Keys + {a});
//   assert a !in (m'.oHeap - m'.m.Keys);
//   var RUSTAN := (m'.oHeap - m'.m.Keys);
//
// AddExtraElement(a, RUSTAN, (RUSTAN + {a}));
//
//   assert ( RUSTAN + {a} ) > (RUSTAN) by {
//     assert a !in RUSTAN;
//     assert a  in RUSTAN + {a};
//   }
//   assert (m'.oHeap - m'.m.Keys + {a}) > (m'.oHeap - m'.m.Keys);
//   assert (m'.oHeap - m'.m.Keys + {a} decreases to m'.oHeap - m'.m.Keys);
//
//
//   assert ofv  in m'.oHeap;
//   assert m'.m.Keys <= m'.oHeap;
//   // if (ofv in m'.m.Keys) {
//   //   AddContainedElement(ofv, m'.m.Keys, (m'.m.Keys+{ofv}));
//   //   assert (m'.m.Keys + {ofv}) == m'.m.Keys;
//   //   RemoveAddContainedElement(m'.oHeap, m'.m.Keys, ofv);
//   //   assert (m'.oHeap - m'.m.Keys + {ofv}) == (m'.oHeap - (m'.m.Keys - {ofv}));
//   // } else {
//   //   assert (ofv !in m'.m.Keys);
//   //   RemoveAddContainedElement(m'.oHeap, m'.m.Keys, ofv);
//   //   assert (m'.oHeap - m'.m.Keys + {ofv}) == (m'.oHeap - (m'.m.Keys - {ofv}));
//   // }
//     RemoveAddContainedElement(m'.oHeap, m'.m.Keys, ofv);
//   assert (m'.oHeap - m'.m.Keys + {ofv}) == (m'.oHeap - (m'.m.Keys - {ofv}));
//   assert (m'.oHeap - m'.m.Keys + {a} decreases to m'.oHeap - m'.m.Keys  + {ofv});




lemma /*VFF*/ XVM_decreases_to_XAO(a : Object, m' : Klon)
  ensures
   (m'.oHeap - m'.m.Keys + {a}, |a.AMFO|, |a.fields.Keys|, 20 //Klone_Via_Map
    decreases to (m'.oHeap - m'.m.Keys), |a.AMFO|, |a.fields.Keys|, 12)
{}





function fielddiff(a : Object, b : Object) : nat
  reads a, b
  {| a.fields.Keys - b.fields.Keys |}


lemma {:verify false} BiggerIsStrictlyBigger<T>(aa : set<T>, bb : set<T>)
     requires aa > bb
     ensures |aa| > |bb|
{
  var xs := aa - bb;
  assert xs > {};
  assert |xs| > 0;
  assert |xs| >= 1;
  assert |aa| == |bb| + |xs|;
  assert |aa| >= |bb| + 1;
}

// lemma {:isolate_assertions} hereWeGoYetAFuckingGain(a : Owner, b : Owner, c: Owner, d: Owner, m : Klon)
//     requires m.SuperCalidFragilistic()
//     requires m.apoCalidse()
//     requires a <= m.m.Keys
//     requires b <= m.m.Keys
//     requires flatten(a)  > m.o.AMFO ///hmmm
//        //t
//
//     requires flatten(a) >= flatten(b)
//     requires c == mapThruKlon(a, m)
//     requires d == mapThruKlon(b, m)
//
//     ensures flatten(c) >= flatten(d)
//     {
//       var f_a := flatten(a);
//       var f_b := flatten(b);
//       var f_c := flatten(c);
//       var f_d := flatten(d);
//
//       assert f_a > m.o.AMFO;
//
//       if (f_b > m.o.AMFO)
//         {
//             assert f_a >= f_b;
//             assert f_c <= f_d; // ARGH ARH ASSAXXUME
//             return;
//         }
//
//     }

lemma Flatten3(a : Owner, b : Owner, c : Owner)
    requires a + b == c
    ensures flatten(a) + flatten(b) == flatten(c)
    {}

lemma Flatten4(a : Owner, b : Owner, c : Owner, m : Klon)
    requires a + b == c
    requires a <= m.m.Keys
    requires b <= m.m.Keys
    requires c <= m.m.Keys
    ensures mapThruKlon(a,m) + mapThruKlon(b,m) == mapThruKlon(c,m)
    {}

// function {:isolate_assertions} moved_computeOwnerAndBoundForNewSubobjectInsideClone(a: Object, m : Klon) : (rv : (Owner, Owner))
//   // does what it says: come up with ownership for a clone of a..\
//     requires m.SuperCalidFragilistic()
//     requires m.apoCalidse()
//     requires m.objectReadyInKlown(a)
//     requires strictlyInside(a, m.o)
//      ensures a != m.o //belt and braces!
//      ensures flatten(rv.0) >= flatten(rv.1)
//
//      reads m.oHeap, m.m.Values
//   {
//     assert a.AMFO > a.AMFX >= a.AMFB >= collectBounds(a.AMFX) >= m.o.AMFB;
//     assert flatten(a.owner) >= flatten(a.bound);
//
//     var rowner := computeOwnerForClone(a.owner, m);
//     var rbound := computeOwnerForClone(a.bound, m );
//     // var rowner := (set o <- a.owner :: m.m[o]);
//     // var rbound := (set o <- a.bound :: m.m[o]);
//     var rAMFX  := flatten(rowner);
//     var rAMFB  := flatten(rbound);
//     var rCOFB  := collectBounds(rAMFB);
//
//
//
//
//     assert rAMFX >= rAMFB;
//     assert rAMFB >= rCOFB;
//     assert rCOFB >= m.o.AMFB;
//     assert rAMFX >= rAMFB >= rCOFB >= m.o.AMFB;
//
//
//
//     assert flatten(rowner) >= flatten(rbound);
//
//     (rowner, rbound)
//   }



// lemma {:isolate_assertions} ownerAndBoundDoingTheMaths(
//                a : Object,
//           rowner : Owner, rbound : Owner,
//            rAMFX : OWNR,   rAMFB : OWNR,   rCOFB : OWNR,
//                m : Klon)
//     requires m.SuperCalidFragilistic()
//     requires m.apoCalidse()
//     requires m.objectReadyInKlown(a)
//     requires strictlyInside(a, m.o)
//
//     requires m.m.Keys >= a.AMFX >= a.AMFB
//
//      ensures a != m.o //belt and braces!
//
//
//     requires a.AMFO > a.AMFX >= a.AMFB >= collectBounds(a.AMFX) >= m.o.AMFB
//
//     requires rAMFX == flatten(rowner)
//     requires rAMFB == flatten(rbound)
//     requires rCOFB == collectBounds(rAMFX)
//      ensures rAMFX >= rAMFB >= rCOFB >= m.o.AMFB
// {
//     //standard ownership relations from a
//     assert a.Ready();
//     assert a.AMFX == flatten(a.owner);
//     assert a.AMFB == flatten(a.bound);
//     assert a.AMFX >= a.AMFB;
//     assert flatten(a.owner) >= flatten(a.bound);
//     assert a.AMFB >= collectBounds(a.AMFX);
//
//     assert StandardOwnershipRelations(a);
//
//     var mAMFX := mapThruKlon(a.AMFX, m);
//     var mAMFB := mapThruKlon(a.AMFB, m);
//
//     assert a.AMFX >= a.AMFB;
//     MapThruKlonGEQ(a.AMFX, a.AMFB, m);
//     assert mAMFX >= mAMFB;
//
//
//
//     //stanrd ownership relationships for forthcoming object
//     assert rAMFX == flatten(rowner);
//     assert rAMFB == flatten(rbound);
//     assert rAMFX >= rAMFB;
//     assert flatten(rowner) >= flatten(rbound);
//     assert rAMFB >= rCOFB;
//
//     assert rAMFX >= rAMFB >= rCOFB >= m.o.AMFB;
// }

predicate StandardOwnershipRelations(a : Object) {
    && a.Ready()
    && a.AMFX == flatten(a.owner)
    && a.AMFB == flatten(a.bound)
    && a.AMFX >= a.AMFB
    && flatten(a.owner) >= flatten(a.bound)
    && nuBoundsOK(a.owner, a.bound)
}
//
// lemma {:isolate_assertions} collectedBoundsAreFlatEnough(a : Owner, b : Owner, m : Klon)
//     requires m.SuperCalidFragilistic()
//     requires m.apoCalidse()
//     requires forall o <- a :: m.objectReadyInKlown(o)
//     requires isFlat(a)
//     requires forall o <- a :: o.Ready()
//     requires b == collectBounds(a)
//     requires forall o <- a :: isFlat(o.AMFB)
//   //  ensures  isFlat(b)
// {
//     assert  b == (set o <- a, oo <- o.AMFB :: oo);
//
//     assert forall o <- a :: isFlat(o.AMFB);
//
//     assert forall o <- b, oo <- o.AMFB :: oo in b;
//     assert forall o <- b, oo <- o.AMFB, ooo <- oo.AMFO :: ooo in b;
//   //  assert isFuckingFlatEnough(b);
// }


lemma FuckingFlatFuckingTown1(a : Owner)
  requires forall o <- a :: o.Ready()
  requires forall o <- a, oo <- o.AMFO, ooo <- oo.AMFO :: ooo in a
   ensures forall o <- a, oo <- o.AMFO :: oo in a
   ensures isFlat(a)
{}

// lemma  {:isolate_assertions} FuckingFlatFuckingTown2(a : Owner)
//   requires forall o <- a :: o.Ready()
// //  requires forall o <- a :: isFlat({o})
//   requires forall o <- a :: isFlat(o.AMFB)
//   //  ensures forall o <- a, oo <- o.AMFO :: oo in a
//   //  ensures isFlat(a)
// {}

//
// lemma  {:isolate_assertions} FuckingFlatFuckingTown3(a : Owner, b : Owner)
//   requires b == flatten(a)
//    ensures isFlat(b)
//    {}
//
//








































































//////////          //////////          //////////          //////////          //////////
          //////////          //////////          //////////          //////////
//////////          //////////          //////////          //////////          //////////

// FAKE method headers start here.
// they do nothing pretty much
// so they should always work :-)
// replace a potentially recuyrsive call with a "FAKE" call.

//////////          //////////          //////////          //////////          //////////
          //////////          //////////          //////////          //////////
//////////          //////////          //////////          //////////          //////////


method {:verify false}  FAKE_Xlone_Via_Map(a : Object, m' : Klon)
  returns (b : Object, m : Klon)
    decreases * //(m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, |a.fields.Keys|, 20 //Klone_Via_Map

    // requires m'.HeapContextReady() && m'.ValuesContextReady()
    // requires m'.SuperCalidFragilistic()
    // requires COKA: COK(a, m'.oHeap) //ties owners into OHEAP but not KLON MAP
    // requires a.Context(m'.oHeap)   requires CTXA: a.Context(m'.oHeap)
    // requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound) //should be in Calid, yeah??
    // requires forall o <- a.AMFO :: o.Ready()
    // requires a.Ready() && a.Valid()
    // requires m'.o.Ready() && m'.o.Valid()
    // requires m'.objectInKlown(m'.o)       ///this meqnas we need to "seed" with the actual clone, rignty
    // requires (m'.ownersInKlown(a) ==> m'.CalidCanKey(a))
    // requires m'.m.Keys <= m'.oHeap //shojld be in Calid?
    // requires a.Ready() && a.Valid()

//FIELD MODEs-ISM HACK -- shouod go into calid or at laets supercalid!
//NO_FIELDMODES   requires forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes

//   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //
//I LOVE YOU BUT I'VE CHOSEN DARKNESS
//FIELD MODEs-ISM HACK -- shouod go into calid or at laets supercalid!
// //ensures removed to try and avoid crash (or gett better diagnosticsc) //I WANT THIS BUT WITHOUT IT I GET CRASHES  - I LOVE YOU BUT I'VE CHOSEN DARKNESS
//NO_FIELDMODES     ensures forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes
//NO_FIELDMODES     ensures unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes )
    ensures m.from(m')
    ensures m.SuperCalidFragilistic()  //moved down from 458
    ensures m.objectInKlown(a)
    ensures m.m[a] == b
//NO_FIELDMODES     ensures b.fieldModes == a.fieldModes
    ensures a.Ready() && a.Valid()
    ensures b.Ready() && b.Valid()
    ensures b.Context(m.hns())
    ensures m.CalidLineKV(a,b)
    ensures HighLineKV(a,b,m)
    ensures HighCalidFragilistic(m)//I WANT THIS BUT WITHOUT IT I GET CRASHES  - I LOVE YOU BUT I'VE CHOSEN DARKNESS
//I LOVE YOU BUT I'VE CHOSEN DARKNESS
    ensures klonReady(m)
    ensures klonLine(a,b,m)
    ensures klonCalid(m)
//   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //


    {
      print "FAKE_Xlone-Via_Map ***FAKE*** ***FAKE*** ***FAKE***\n";
      print "FAKE_Xlone-Via_Map ***FAKE*** ***FAKE*** ***FAKE***\n";
      print "FAKE_Xlone-Via_Map ***FAKE*** ***FAKE*** ***FAKE***\n";

      // // // // // // // // // // // // // // //
      //Calidian Consequences
      assert m'.Calid();
      assert m'.HeapContextReady() && m'.ValuesContextReady();
      assert m'.m.Keys <= m'.oHeap by { reveal m'.Calid(); assert m'.Calid(); } //but it's infucking CALIUKD.
//      assert m'.objectInKlown(m'.o) by { reveal m'.Calid(); assert m'.Calid(); }  //and htis one
      assert m'.o.Ready() && m'.o.Valid()  by { reveal m'.Calid(); assert m'.Calid(); }  //and this one

      // // // // // // // // // // // // // // //
      //and Ready()made reproaches
      assert forall o <- a.AMFO :: o.Ready(); //which I hope isn't circular :-)
        //It's but by a reflexive impl uses AMFX :-)
      // // // // // // // // // // // // // // //
      m := m';
      b := a;
    }





method {:verify false} FAKE_Xlone_Clone_Clone(a : Object, m' : Klon)
  returns (b : Object, m : Klon)
    decreases * //(m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, |a.fields.Keys|, 15

///no reqires, XVM verifiew 17s
// these OJK 44s
  requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound) //should be in calid
  requires a !in m'.m.Keys
  requires inside(a, m'.o) //can c == m'.o

//these OK 54s!
   //START FROM XVM
  requires m'.SuperCalidFragilistic()
  requires m'.apoCalidse()
  requires COKA: COK(a, m'.oHeap) ///includews a.Context(m'.oHeap)

  requires a  in m'.oHeap  //willis
// these OK 35s
  requires a !in m'.m.Keys
//  requires m'.ownersInKlown(a)  //luxon

  //requires (klonCanKV(m',a,a))

//these OK 47s
  requires (m'.c_amfx >= flatten(m'.clbound) >= flatten(m'.o.bound))
  requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound) //should be in cali


//these OK 49s
  requires a.Ready() && a.Valid()
  // requires m'.ownersInKlown(a)
  //  requires m'.CalidCanKey(a)

//FIELD MODEs-ISM HACK -- shouod go into calid or at laets supercalid!
//NO_FIELDMODES   requires forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes
//NO_FIELDMODES    ensures forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes
//NO_FIELDMODES    ensures unchanged( m.oHeap`fieldModes, m.m.Values`fieldModes )

// //END FROM XVM

   ensures m.SuperCalidFragilistic()
   ensures a in m.m.Keys
   ensures m.objectInKlown(a)
   ensures m.m[a] == b
//NO_FIELDMODES x   ensures a.fieldModes  == b.fieldModes
   ensures a.fields.Keys == b.fields.Keys
   ensures b.Ready() && b.Valid()
   ensures b.Context(m.hns())
   ensures m.from(m')
{
  b := a;
  m := m';

      print "FAKE_Xlone-Clone_Clone ***FAKE*** ***FAKE*** ***FAKE***\n";
      print "FAKE_Xlone-Clone_Clone ***FAKE*** ***FAKE*** ***FAKE***\n";
      print "FAKE_Xlone-Clone_Clone ***FAKE*** ***FAKE*** ***FAKE***\n";


}







method  {:verify false} FAKE_Xlone_All_Owners(a : Object,  m' : Klon)  returns (m : Klon)
  decreases * //(m'.oHeap - m'.m.Keys), |a.AMFO|, |a.fields.Keys|, 12

  //we're solely ever called from Xlone_Via_Map  (and could be reintergrated, who knows?)
  requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound)
  requires a !in m'.m.Keys
//  requires inside(a, m'.o)


//START FROM XVM
  requires m'.HeapContextReady() && m'.ValuesContextReady() &&  m'.Calid()
  requires m'.SuperCalidFragilistic()
  requires COKA: COK(a, m'.oHeap)

  //requires (a !in m'.m.Keys) ==> (klonCanKV(m',a,a))
  //requires (klonCanKV(m',a,a))
  requires (m'.c_amfx >= flatten(m'.clbound) >= flatten(m'.o.bound))
  requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound)

  requires forall o <- a.AMFO :: o.Ready()

  requires a.Ready() && a.Valid()
  //requires m'.ownersInKlown(a)
  requires m'.o.Ready() && m'.o.Valid()
  requires m'.objectInKlown(m'.o)
  // requires m'.CalidCanKey(a)
  requires (a  in m'.oHeap)  //willis
  requires (a !in m'.m.Keys) //willis


  requires m'.HeapContextReady()
  requires m'.ValuesContextReady()
  requires m'.Calid()

  requires a in m'.oHeap
  requires m'.m.Keys <= m'.oHeap
//END FROM XVM

//FIELD MODEs-ISM HACK -- shouod go into calid or at laets supercalid!
//NO_FIELDMODES   requires forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes
//NO_FIELDMODES    ensures forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes
//NO_FIELDMODES    ensures unchanged( m.oHeap`fieldModes, m.m.Values`fieldModes )

  ensures  m.from(m')
  ensures  m.SuperCalidFragilistic()
  ensures  m.ownersInKlown(a)
// ensures  a !in m.m.Keys  NOT THIS ONE PROBABLU SHOULDN"T HOLD.






//
//    requires m'.SuperCalidFragilistic()   //does it or not??
//    requires m'.cCanKey(a)    //does it or not?? well does it?
//
//   //we're solely ever called from Xlone_Via_Map  (and could be reintergrated, who knows?)
//   requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound)
//   requires a !in m'.m.Keys
// //  requires inside(a, m'.o)
//
//
// //START FROM XVM
//   requires m'.HeapContextReady() && m'.ValuesContextReady() &&  m'.Calid()
//   requires m'.Calid()
//   requires COKA: COK(a, m'.oHeap)
//
//   //requires (a !in m'.m.Keys) ==> (klonCanKV(m',a,a))
//   requires (klonCanKV(m',a,a))
//   requires (m'.c_amfx >= flatten(m'.clbound) >= flatten(m'.o.bound))
//   requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound)
//
//   requires forall o <- a.AMFO :: o.Ready()
//
//   requires a.Ready() && a.Valid()
//   //requires m'.ownersInKlown(a)
//   requires m'.o.Ready() && m'.o.Valid()
//   requires m'.objectInKlown(m'.o)
//   requires m'.CalidCanKey(a)
//
//   requires m'.HeapContextReady()
//   requires m'.ValuesContextReady()
//   requires m'.Calid()
//
//   requires a in m'.oHeap
//   requires m'.m.Keys <= m'.oHeap
// //END FROM XVM
//
  ensures  m.from(m')
  ensures  m.Calid()
  ensures  m.SuperCalidFragilistic()
  ensures  m.ownersInKlown(a)
{
  //cou;d just recurse primitively here  - try to help come donw...
  m := m';
  /// nor was it possible for me tot restart - e.g.


      print "FAKE_Xlone-All_Owners ***FAKE*** ***FAKE*** ***FAKE**r*\n";
      print "FAKE_Xlone-All_Owners ***FAKE*** ***FAKE*** ***FAKE***\n";
      print "FAKE_Xlone-All_Owners ***FAKE*** ***FAKE*** ***FAKE***\n";
}




method {:verify false} FAKE_Xlone_All_Fields(a : Object, b : Object, m' : Klon)
  returns (m : Klon)

  decreases * //(m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, fielddiff(a,b), 10

  requires a.Ready() && a.Valid()

  //we're just ever called from Xlone_Via_Map  (and could be reintergrated, who knows?)
  requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound)
  requires m'.objectInKlown(a)
  requires inside(a, m'.o)
  requires a in m'.m.Keys
  requires m'.m[a] == b

//START FROM XVM
  requires m'.HeapContextReady() && m'.ValuesContextReady() &&  m'.Calid()
  requires m'.Calid()
  requires m'.SuperCalidFragilistic()
  requires COKA: COK(a, m'.oHeap)

//////////////////////////////////////////////////////////////////////
  //prog WORNG  requires (klonCanKV(m',a,a))

  requires klonVMapOK(m'.m)
//  requires canVMapKV(m'.m, a, b)
  requires (a in m'.oHeap)
  requires (if (b==a) then (b in m'.oHeap) else (b !in m'.oHeap))
  requires a.Ready() && a.Valid() && a.Context(m'.oHeap)
  requires b.Ready() && b.Valid() && b.Context(m'.hns({b}))
  requires m'.ownersInKlown(a)
//NO_FIELDMODES   requires a.fieldModes == b.fieldModes
  requires (b.AMFX >= b.AMFB >= a.AMFB)

//////////////////////////////////////////////////////////////////////


  requires (m'.c_amfx >= flatten(m'.clbound) >= flatten(m'.o.bound))
  requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound)

  requires forall o <- a.AMFO :: o.Ready()

  requires a.Ready() && a.Valid()
  requires m'.ownersInKlown(a)  //prog??
  requires m'.o.Ready() && m'.o.Valid()
  requires m'.objectInKlown(m'.o)
  //requires m'.CalidCanKey(a)  //prog

  requires m'.HeapContextReady()
  requires m'.ValuesContextReady()
  requires m'.Calid()

  requires a in m'.oHeap
  requires b !in m'.oHeap
  requires b in m'.hns()
  requires m'.m.Keys <= m'.oHeap
  requires allocated(m'.oHeap)
//END FROM XVM

//FIELD MODEs-ISM HACK -- shouod go into calid or at laets supercalid!
//NO_FIELDMODES   requires forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes
//NO_FIELDMODES    ensures forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes
//NO_FIELDMODES    ensures unchanged( m.oHeap`fieldModes, m.m.Values`fieldModes )


//progTODOFUCK  ensures  m.from(m')
  ensures  m.Calid()
  ensures  m.from(m')
  ensures  m.ownersInKlown(a)
  ensures  a in m.m.Keys
  ensures  a.fields.Keys == b.fields.Keys
//NO_FIELDMODES   ensures  a.fieldModes  == b.fieldModes
  ensures  m.m[a] == b
  ensures  a.Ready() && a.Valid() && a.Context(m.hns())
  ensures  b.Ready() && b.Valid()
  ensures  b.Context(m.hns())

  //ensures  m.m.Values >= m'.m.Values + {b}

  modifies b`fields
{
      print "FAKE_Xlone_All_Fields ***FAKE*** ***FAKE*** ***FAKE***\n";
      print "FAKE_Xlone_All_Fields ***FAKE*** ***FAKE*** ***FAKE***\n";
      print "FAKE_Xlone_All_Fields ***FAKE*** ***FAKE*** ***FAKE***\n";
  m := m';
}


//2 in 2212-2213, 1 in 2227-2245
method {:verify false}  FAKE_Xlone_Field_Map(a : Object, n : string, b : Object, m' : Klon)
  returns (m : Klon)

  decreases * //(m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, fielddiff(a,b), 5 //Xlone_Field_Map
  // progTODOFUCKED

  requires n  in a.fields.Keys
  requires n !in b.fields.Keys
//NO_FIELDMODES   requires a.fieldModes.Keys == b.fieldModes.Keys
  requires a.Ready() && a.Valid()

    // we're just called from Xlone_Via_Map  (and could be reintergrated, who knows?)
//2 ERRPRS & likely WRONG - are you sureabout that? 2sep 2025
  requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound) ///coudl be in calid yeah??

  requires a in m'.m.Keys
  requires m'.m[a] == b
  requires m'.objectInKlown(a)
  requires inside(a, m'.o)

//START FROM XVM
  requires m'.HeapContextReady() && m'.ValuesContextReady()
  requires m'.Calid()
  requires COKA: COK(a, m'.oHeap)

  requires (m'.c_amfx >= flatten(m'.clbound) >= flatten(m'.o.bound))
//error & likely#WRONG // requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound) //HUH?  WHY is this wrong? 2sep2025

  requires forall o <- a.AMFO :: o.Ready()

  requires a.Ready() && a.Valid()

//   //surely much of the following comes down from Calid()?
  requires m'.o.Ready() && m'.o.Valid()
  requires m'.objectInKlown(m'.o)
//requires m'.CalidCanKey(a) //error & WRONG - a must already be in the thing

  requires m'.HeapContextReady()
  requires m'.ValuesContextReady()
  requires m'.Calid()

  requires a  in m'.oHeap
  requires b !in m'.oHeap
  requires b in m'.hns()
  requires m'.m.Keys <= m'.oHeap
  requires allocated(m'.oHeap)
// //END FROM XVM


//NO_FIELDMODES   requires a.fieldModes.Keys == b.fieldModes.Keys
//NO_FIELDMODES   requires n in b.fieldModes.Keys

//FIELD MODEs-ISM HACK -- shouod go into calid or at laets supercalid!
//NO_FIELDMODES   requires forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes
//NO_FIELDMODES    ensures forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes
//NO_FIELDMODES    ensures unchanged( m.oHeap`fieldModes, m.m.Values`fieldModes )

   ensures old(fielddiff(a,b)) decreases to fielddiff(a,b)


  ensures  m.from(m')
  ensures  m.SuperCalidFragilistic()
  ensures  m.ownersInKlown(a)
  ensures  a in m.m.Keys
  ensures  n in a.fields.Keys
  ensures  n in b.fields.Keys
  ensures  old(fielddiff(a,b)) decreases to fielddiff(a,b)
  ensures  b.fields.Keys == old(b.fields.Keys) + {n}
  ensures  m.m[a] == b
  ensures  m.m[ a.fields[n] ] == b.fields[n]
  ensures  m.m[ a.fields[n] ] == m.m[a].fields[n]  //prog THIS IS THE KEY POSTCONDITION!!
//NO_FIELDMODES   ensures a.fieldModes.Keys == b.fieldModes.Keys


  ensures unchanged( m'.oHeap )
  ensures unchanged( m.oHeap  )
  ensures unchanged( m.oHeap`fields )
  ensures allocated( m'.oHeap )
  ensures allocated( m.oHeap  )
  ensures unchanged(m'.oHeap`fields)

  ensures m.oHeap == m'.oHeap


  modifies b`fields
{
      print "FAKE_Xlone_Field_Map ***FAKE*** ***FAKE*** ***FAKE***\n";
      print "FAKE_Xlone_Field_Map ***FAKE*** ***FAKE*** ***FAKE***\n";
      print "FAKE_Xlone_Field_Map ***FAKE*** ***FAKE*** ***FAKE***\n";

   m := m';
}

function allThemModes(m : Klon) : map<Object,map<string,Mode>>
//NO_FIELDMODES   reads m.hns()`fieldModes
//  reads m.m.Keys`fieldModes, m.m.Values`fieldModes
{
  map[]
//NO_FIELDMODES   map o <- m.hns() :: o.fieldModes
 // (map o <- m.m.Keys :: o.fieldModes) + (map o <- m.m.Keys :: m.m[o].fieldModes)
}

lemma {:isolate_assertions} FieldModesAreStillOK(a : Object, b : Object, m : Klon, m' : Klon)
  // given a & b fields modes are equal, addimg them into m' giving m doesn't change anything
  // that's to say, doesn't chanfe ANY of the existing Klon fielModea mappings

  // requires a.fieldModes == b.fieldModes
  // requires m'.CKV_preconditions(a,b)
  // requires m == m'.CalidKV(a,b)
  // requires forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes
  //  ensures forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes
{
  // forall z <- m.m.Keys ensures (z.fieldModes == m.m[z].fieldModes)
  // //by
  // {
  //   if (z in m'.m.Keys)
  //     { assert forall y <- m'.m.Keys :: y.fieldModes == m'.m[y].fieldModes;
  //       assert z.fieldModes == m'.m[z].fieldModes;
  //       assert forall y <- m'.m.Keys :: m.m[y] == m'.m[y];
  //       assert z.fieldModes == m.m[z].fieldModes;
  //     }
  //     else
  //     {
  //       assert z == a;
  //       assert m.m[z] == b;
  //       assert a.fieldModes == b.fieldModes;
  //       assert z.fieldModes == m.m[z].fieldModes;
  //     }
  // }
  // assert forall z <- m.m.Keys :: z.fieldModes == m.m[z].fieldModes;
}





 lemma {:isolate_assertions} CalidKVFromHighLineKV(k : Object, v : Object, m : Klon)
   requires m.apoCalidse()
   requires m.SuperCalidFragilistic()
   requires HighCalidFragilistic(m)
   requires HighLineKV(k,v,m)
    ensures m.CalidLineKV(k,v)
    {}



lemma SetDJNZ<T>(a : set<T>, b : set<T>)
  requires a > {}
  requires b >= a
   ensures b > {}
{}


   lemma ItMustBI(f : Object, t : Object, pivot : Object)
     requires f.Ready() requires t.Ready() requires pivot.Ready()

      requires strictlyInside(f, pivot)
      requires outside(t, pivot)
      requires refOK(f,t)

      ensures f != t

      ensures not( t.AMFO >= pivot.AMFO )
      ensures f.AMFO >= pivot.AMFO
      ensures not( t.AMFO >= f.AMFO)
      ensures f !in t.owner
      ensures not(refDI(f,t))

      ensures refBI(f,t)
      ensures (f.AMFB > {})
      ensures (f.AMFB >=  t.AMFX)
     { }








  lemma {:isolate_assertions}  RefOKGetsModeOK(source : Object, clone : Object, n : string, t : Object, u : Object, m : Klon)
  //   //cloning source.Valid() && source.Context(context) results in clone.Valid() && clone.Context(context)
  //takes ages even just to resolve, let alone veryify. crashes regularly on the new versions
  //9 Feb 2026
    requires inside(source, m.o)   //note not strictly.
    requires source.Ready()
    requires source.Valid()   ///note this!1
    requires clone.Ready()
    requires t.Ready()
    requires u.Ready()
    requires m.objectInKlown(t)
    requires m.objectInKlown(source)
    requires m.apoCalidse()   ///note making a choice about what provision we need
                             ///turning it on lets it work.
    //  requires m.SuperCalidFragilistic()
    //  requires HighLineCalid(m)
        requires m.CalidOwners()


    requires refOK(source, t)
    requires refOK(clone, u)

    requires m.objectInKlown(source)
    requires clone == m.m[ source ]
      requires n in source.fields.Keys
      requires t == source.fields[n]
      // requires n in clone.fields.Keys
//NO_FIELDMODES     requires n in source.fieldModes.Keys
//NO_FIELDMODES     requires n in  clone.fieldModes.Keys
      // requires u == clone.fields[n]
      // requires t in m.m.Keys
      // requires u == m.m[ t ]

    requires clone != source
    requires outside(t, clone)  ///this is fine: the original.t can't be inside the clone...

      // requires clone.fields[n] == m.m[ t ]
      // requires clone.fields[n] == m.m[ source.fields[n] ]
      // requires m.m[ source ].fields[n] == m.m[ source.fields[n] ]

///    requires source != m.o
    requires inside(t,source) || outside(t,source) //colinearity?
      //are we sure about that?

//    requires strictlyInside(t, source) //hmm, should try with inside not strictlyInside?
    requires m.ValuesOwnersReady()
  ///NOOOO WRONG!  requires forall oo <- t.owner :: strictlyInside(oo, m.o)

//NO_FIELDMODES     requires modeOK(source, source.fieldModes[n], t) //YES THIS
//NO_FIELDMODES     requires source.fieldModes == clone.fieldModes //technically overkill...
//NO_FIELDMODES     requires source.fieldModes[n] == clone.fieldModes[n] //less overkill version


    requires HighLineKV(t,u,m)
//    requires mappingOWNRsThruKlownKV(t.owner, u.owner, m)  ///after the money's gone
  //  requires mappingOwnersThruKlownKV(t,u,m);
    // requires mappingOWNRsThruKlownKV(t.AMFO, u.AMFO, m)
    // requires mappingOWNRsThruKlownKV(source.AMFO, clone.AMFO, m)
    // requires mappingOWNRsThruKlownKV(source.AMFB, clone.AMFB, m)
    // requires mappingOWNRsThruKlownKV(t.AMFX, u.AMFX, m)

//    requires sameMode(source.fieldModes[n], clone.fieldModes[n])//9 Feb 2026
//    requires sameRef(source, t, clone, u)
//       ensures modeOK(clone,  clone.fieldModes[n], u)
  {
    // match (clone.fieldModes[n])
    //     case Evil => assert modeOK(clone, clone.fieldModes[n], u);
    //     case Rep | Owned(_) | Loaned(_) =>
    //            assert refDI(source,t);
    //            assert source in t.owner;
    //            assert clone  in u.owner;
    //            assert refDI(clone,u);
    //            assert modeOK(clone, clone.fieldModes[n], u);
    //     case Peer =>
    //            //assert refBI(source,t);
    //            assert mappingOwnersThruKlownKV(source, clone, m);
    //            assert mappingOwnersThruKlownKV(t, u, m);
    //            assert source.owner == t.owner;
    //            assert m.apoCalidse();
    //            assert source.owner <= m.m.Keys;
    //            if (inside(t,source))
    //               {
    //                   assert t.owner == m.o.owner == source.owner;
    //                   assert clone.owner == m.clowner;
    //                   assert inside(u, clone);
    //                   assert mappingOWNRsThruKlownKV(source.owner, clone.owner, m);
    //                   assert mappingOWNRsThruKlownKV(t.owner, u.owner, m);
    //                   assert clone.owner == u.owner;
    //                   assert modeOK(clone, clone.fieldModes[n], u);
    //               } else {
    //                  assert t == u;
    //                  assert refBI(source, t);
    //                  assert refBI(clone, u);
    //                  assert modeOK(clone, clone.fieldModes[n], u);
    //               }
    //            assert modeOK(clone, clone.fieldModes[n], u);
    //     case Borrow(_,_,_,_) =>
    //            assert refOK(source,t);
    //            assert (source==t) || refBI(source,t) || refDI(source,t);
    //            assert (source==t) ==> (clone==u);
    //            assert refBI(source,t)  ==> refBI(clone, u);
    //            assert refDI(source,t)  ==> refDI(clone, u);
    //            assert (clone==u)  || refBI(clone, u) || refDI(clone, u);
    //            assert refOK(clone, u);
    //            assert modeOK(clone, clone.fieldModes[n], u);
    //     case Self =>
    //            assert source == t;
    //            assert  clone == u;
    //            assert modeOK(clone, clone.fieldModes[n], u);
    }
