include "Xlone.dfy"

include "Klon-Lemmata.dfy"


//{:timeLimit 300}
method {:isolate_assertions} {:verify true} Xlone_Clone_Clone(k : Object, m' : Klon)
  returns (v : Object, m : Klon)
  //this is pretty close to a "shallow clone" - acutally a "strucural clone" -
  //clowning all owners etc but leaving the fields all empty
  //we're solely called from Xlone_Via_Map  (and could be reintergrated, who knows?)
  decreases * //(m'.oHeap - m'.m.Keys + {k}), |k.AMFO|, |k.fields.Keys|, 15

  requires k !in m'.m.Keys
  requires strictlyInside(k, m'.o) //can c == m'.o  -- NO!!!

  requires klonReady(m')
  requires klonCalid(m')

  requires COK(k, m'.oHeap)   requires COKA: COK(k, m'.oHeap)

  //////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////
  //random shit May 5 2026
  requires m'.ownersInKlown(k)
  /////////////////////////////////////////////////////////////////////

//FIELD MODEs-ISM HACK -- shouod go into calid or at laets supercalid!
//NO_FIELDMODES  requires forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes
//

//THURSDAY NO ENSURES - 24 FEB 2026
//FUCKTODO
//NO_FIELDMODES    ensures forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes
//NO_FIELDMODES    ensures unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes )

//NOENSURES
  //  ensures klonReady(m)
  //  ensures klonCalid(m)
  //  ensures m.from(m')
  //  ensures m.objectInKlown(k)
  //  ensures m.m[k] == v
  //  ensures v.Context(m.hns())
  //  ensures klonLine(k,v,m)

//NOENSURES     ensures m.SuperCalidFragilistic()
//NOENSURES     ensures HighCalidFragilistic(m)
//NOENSURES
//NOENSURES     ensures m.from(m')
//NOENSURES     ensures m.objectInKlown(k)
//NOENSURES     ensures m.m[k] == v
//NOENSURES //NO_FIELDMODES   ensures k.fieldModes  == v.fieldModes   //hmm shouldbe some kind of map.  mapping modes?
//NOENSURES     ensures v.Ready() && v.Valid()
//NOENSURES     ensures v.Context(m.hns())
//NOENSURES     ensures m.CalidLineKV(k,v)   //JDVANCE
//NOENSURES     ensures HighLineKV(k,v,m)       //TUESDAY


//FUCKTODO - comnmented out before 29 Feb..
//    ensures v.fields.Keys == k.fields.Keys ....   //KEYS
//     or istKlonAlleFelder(k,v,m)... or somethinbg.
      //this one is tricky
      //the code *will* clone all objects fields eventually.
      //BUT this may only hold at the very very end!
      //consider k "pivot" object { fa == .. lots and lots of stuff, every object which points back to the root;  fb == 42. }
      //if you copy fa and fb in alphabetical order, the EVERY recursive call finds we've started copying the root
      //will finish *without* filling in all the fields...  knowing they'lll be done later.
      //whichever method actually guarantees theyll be done later should do soethign abotu this.
      //could track this with an extra ghost field n the Klon.  or, I dunno. something??
{

  print "PRECALL Clone_Clone_CLone of:", fmtobj(k), " owned by ", fmtown(k.owner) ,"\n";

var rm := m';
    m  := m';
    v  := k;

assert klonReady(rm);
assert klonCalid(rm);

  print "CALL Clone_Clone_CLone of:", fmtobj(k), " owned by ", fmtown(k.owner) ,"\n";
//  print "VARIANT CCC ", |(m'.oHeap - m'.m.Keys)|, " ", |k.AMFO|, " ", |(k.fields.Keys)|, " ", 15, "\n";
  print "VARIANT CCC ", |(m'.oHeap - m'.m.Keys +  {k})|, " ", |k.AMFO|, " ", |(k.fields.Keys)|, " ", 15, "\n";

  print "Clone_Clone_Clone ", fmtobj(k), " precall CAO ", fmtown(k.owner) ,"\n";
//  printmapping(m'.m);

///////////////////////////////////////////////////////////////////////// ////////

  XCC_decreases_to_XAO(m',k);

  print "Clone_Clone_Clone ", fmtobj(k), " calling CAO ", fmtown(k.owner) ,"\n";
///////////////////////////////////////////////////////////////////////// ////////


   rm := /*FAKE_*/Xlone_All_Owners(k, m');

//////////////////////////////////////////////////////////////
  print "Clone_Clone_Clone ", fmtobj(k), " back from CAO ", fmtown(k.owner) ,"\n";
  print "CCC rm.owersInKlown ", fmtobj(k), " = ", rm.ownersInKlown(k), "\n";
  print "CCC k in rm.m.Keys ", fmtobj(k), " = ", (k in rm.m.Keys), "\n";


   assert rm.ownersInKlown(k);

  if (k in rm.m.Keys) {
     print "CCC we got it\n";

    m := rm;
    v := m.m[k];
//NO_FIELDMODES           assert unchanged(m'.oHeap`fieldModes, m'.m.Values`fieldModes );


        print "RETN Clone_Clone_CLone ", fmtobj(k), " already cloned: abandoning ship!!\n";

        return;
  } // k in rm.m.Keys - i.e.   done while cloning owners



print "CCC 1001 HERE! WEESA HERE!\n";

   assert k !in rm.m.Keys;
   assert k in rm.oHeap by { reveal COKA; }
   assert klonReady(rm);
   assert klonCalid(rm);
   assert rm.ownersInKlown(k);
   assert rm.from(m');

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

//     print (rm.m.Keys <= rm.oHeap);
//     print (rm.m.Values <= rm.hns());
//     print (rm.objectReadyInKlown(rm.o));
// ///    print (rm.HeapOwnersReady());
// ///    print (rm.c_amfx <= rm.oHeap);
// ///  print rm.apoCalidse();
//   print (k.owner <= rm.m.Keys);
// //  print rm.SuperCalidFragilistic();
//   nl();

  k.ExtraReady();
  // var rowner := mapThruKlon(k.owner, rm); ///dunno when I wrote it but...
  // var rbound := mapThruKlon(k.bound, rm);

// {
//   var m := rm;
//   assert m.apoCalidse() ;
//   assert k.owner <= m.m.Keys;
//         assert rm.HeapContextReady();
//         assert rm.ValuesContextReady();
//         assert rm.Calid();
//
//   assert m.SuperCalidFragilistic();
// }

assert nuBoundsOK(k.owner,k.bound);
  var rowner := mapThruKlon(k.owner, rm); ///dunno when I wrote it but...
//var rowner := computeOwnerForClone(k.owner, rm); ///dunno when I wrote it but...
//var rbound := computeOwnerForClone(k.bound, rm);

assert AllReady(rowner);
//  var rbound := proposeBounds(rowner);
var rbound := mapThruKlon(k.bound, rm);
assert nuBoundsOK(rowner,rbound);
  var context := rm.hns();


 print "CCC mapped=", fmtown(rowner), " bound=", fmtown(rbound), "\n";


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
  print "Clone_Clone_CLone ", fmtobj(k), " have rowner ", fmtown(rowner) ," self not yet cloned\n";
//
//
//   assert  COK(k,  m'.oHeap);
//   assert  COK(k,  rm.oHeap);
//   assert  COK(k, rrm.oHeap);
//
//   //FUCKTODO
//   // assert forall z <- rrm.m.Keys :: z.fieldModes == rrm.m[z].fieldModes;
//   // assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
//   //FUCKTODO
//
print "Clone_Clone_Clone ", fmtobj(k), " boodle boodle boodle\n";
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
// assert context == rrm.hns();
//
// print "CALLING MAKE...";
//
// //FUCKTODO
// //
// //
// // assert rrm.preCalid();
// // assert rrm.preCalid2();
// // assert flatten(rrm.o.bound) == rrm.o.AMFB;
// // assert flatten(rrm.clbound) >= rrm.o.AMFB;
// // assert (rrm.o.AMFB >= collectBounds(rrm.o.AMFX));
// //
// // //random bounding shit
// // // assert flatten(rbound) >= k.AMFB; //THIS ONE BOUNDNEST
// //
// // assert k.AMFB >= rrm.o.AMFB;
// //    //should only be copyhin stuff that's INSIDE.
// //       //except that's not what this doese!
// //   //aee stuff eaerlier - ThereIsNoSpoon…
// //
// //
// // //precalid
// // assert (flatten(rrm.clbound) >= rrm.o.AMFB);
// // assert (rrm.c_amfx >= flatten(rrm.clbound) >= rrm.o.AMFB);
// //
// // //dunno.  from above hack?
// // ///assert (flatten(rbound) >= flatten(k.bound));  //BOUNDNEST
// //
// // /////////////////////////////////////////////////////////
// // //general preconditions assertions that might be useful.
// //
// //   assert rrm.SuperCalidFragilistic();
// //      //NOT needed for make - nor should it be, becausr
// //      //Calid only applies when in the middle of k Clone
// //      //but make can be acled jut to bild stuf..
// //
// //
// //   assert COK(k, rrm.oHeap);
// //   assert k.Ready();
// //   assert k.Context(rrm.oHeap);
// // //  assert rrm.hns() >= flatten(rowner);  ??prog 12 July 2025 - why is this here?
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
//   // assert forall z <- rrm.m.Keys :: z.fieldModes == rrm.m[z].fieldModes;
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
   assert nuBoundsOK(rowner, rbound);  ///TRUMP TRUMPP TRUMPPP
//
   assert klonReady(rm);
   assert klonCalid(rm);


///make preconditions - 4 May 2026
    assert AllReady(rowner);    //when was this deleted?
    assert AllReady(rbound);     //because of this? who knows!
    //NOCONTEXT  requires /* context >= */ flatten(rowner) >= flatten(rbound)   //FUCK_CONTEXT!!!
    assert flatten(rowner) >= flatten(rbound);
    assert nuBoundsOK(rowner, rbound);   ///attempting to get verification times down

// //// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
// // /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
  v := new Object.make(k.fieldModes, rowner, context, "clone_of_" + k.nick, rbound);
print "BACK FROM MAKE with ",fmtobj(v)," owner=", fmtown(v.owner),"\n";
// //// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
// // /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///


    assert k.Ready();
    assert m.ownersInKlown(k);
    assert klonReady(rm);
    assert strictlyInside(k, rm.o);
    assert (v.owner == (mapThruKlon(k.owner, rm)));
    assert (v.bound == (mapThruKlon(k.bound, rm)));

MappedBounds(k,v,rm);

///// hmm...
  //  assert klonReady(rm);
  //  assert klonCalid(rm);
  //  assert m.ownersReadyInKlown(k);
  //  assert k in rm.oHeap by { reveal COKA; }
  //  assert k !in rm.m.Keys;
  //  assert fresh(v);
  //  assert v !in rm.m.Values;
//
// {
//  var m := rm;
//  reveal COK(); assert COK(k, m'.oHeap) by { reveal COKA; }
// assert k.Ready(); assert (k.AMFO   >  k.AMFB);
//  assert
//     && (k.Ready() && k in m.oHeap    && k.Valid() && k.Context(m.oHeap))
//   && (v.Ready() && v in m.hns({v}) && v.Valid() && v.Context(m.hns({v})))
//
//   && (m.m.Keys >= k.AMFX)
//   && (k.AMFO   >  k.AMFB) //nuclear war is good
//   && (v.AMFO   >= v.AMFB) //nuclear war is good
//   && (v.AMFB   >= k.AMFB)
// ;
//
// assert  && (m.o.Ready())           //precond?
//   && (m.objectInKlown(m.o))  //precond?
//
//   && ( (k == m.o)       <==>  (v == m.c)  )
//   && ((inside(k, m.o))   ==> (k.AMFB  <= m.o.AMFB)) //hmmmm //GREENLAND
//   && (outside(k, m.o)   <==>  (v == k))
//   && ( inside(k, m.o)   <==>  inside(v, m.c) )
//   && (outside(k, m.c))
//   && ((inside(k,m.o)) ==> (v !in m.oHeap))
//   ;
//
//
// assert
//   && (m.ownersReadyInKlown(k))
//   && (m.objectReadyInKlown(m.o))
//
//   && (if (k == m.o) then (
//                            && (k != v)
//                            && (v == m.c)
//                            && (v.owner == m.clowner)
//                            && (v.bound == m.clbound)
//
//                          ) else if (outside(k, m.o) )
//       then (
//                           assert k != m.o;
//                           k == v
//      ) else (
//           assert strictlyInside(k, m.o);
//           assert k != m.o;
//           && (k != v)
//           && (v.bound == mapThruKlon(k.bound, m))
//           && (v.owner == mapThruKlon(k.owner, m))
//         ));
//
//
// }
   assert klonBound(k,v,rm);
   assert klonModes(k,v,rm);
   assert klonGeometry(k,v,rm);
   assert klonIdentity(k,v,rm);

   assert klonLine(k,v,rm);

//    assert m'.o == rm.o;
//    assert strictlyInside(k, rm.o);
//    assert k != rm.o;
//    assert v != rm.m[rm.o];
//    assert ( (k == rm.o)     <==>  (v == rm.m[rm.o])  );
//
//    assert forall x <- rm.m.Keys :: ( (x == rm.o)     <==>  (rm.m[x] == rm.m[rm.o])  );
//



// //JDVANCE
// assert strictlyInside(k, m'.o);
// assert strictlyInside(k, rrm.o);
//
//
//     assert (k.Ready());
//     assert (rrm.ownersInKlown(k));
//     assert (k in rrm.oHeap);
//     assert (v.Ready());
//     assert (v in rrm.hns({v}));
//     assert (v.AMFO  >= v.AMFB);
//     assert (v.AMFB >= k.AMFB);     ///JDVANCE
//     assert ( inside(k,rrm.o) );
//     assert (   (inside(k,rrm.o)) ==> (k.AMFB  >= rrm.o.AMFB));
//     assert (not(inside(k,rrm.o)) ==> (v == k));
//     assert (   (inside(k,rrm.o)) ==> ((v !in rrm.oHeap)) );
//     assert (mappingOwnersThruKlownKV(k,v,rrm));     ///JDVANCE
//
//
//   assert ( inside(k,rrm.o) );
//   assert (not(inside(k,rrm.o)) ==> (3 == 2));
//
//   assert rrm.OwnersLineKV(k,v);
//   assert  COK(k,  m'.oHeap);
//   assert  COK(k,  rm.oHeap);
//   assert  COK(k, rrm.oHeap);
//
//
//   //FUCKTODO
//   // assert k.fieldModes  == v.fieldModes;
//   // assert unchanged( rrm.oHeap`fieldModes, rrm.m.Values`fieldModes );
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
//   //   assert v !in rrm.oHeap;
//   //   assert v.AMFO >= v.AMFX >= v.AMFB;
//   //
//   //   assert v.fieldModes == k.fieldModes;
//   //   assert unchanged( rrm.oHeap`fieldModes, rrm.m.Values`fieldModes );
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
//     // assert  (v.AMFO >= v.AMFB >= k.AMFB >= rrm.o.AMFB) ;
//     //
//     //  //THIS ONE
//     // assert  (v.AMFO >= v.AMFB >= collectBounds(v.AMFX));
//     // // assert  collectBounds(v.AMFX) >= k.AMFB;
//     // assert  v.AMFB >= k.AMFB;
//     // assert  k.AMFB >= rrm.o.AMFB;
//     //
//     // assert forall z <- rrm.m.Keys :: z.fieldModes == rrm.m[z].fieldModes;
//     // assert unchanged( rrm.oHeap`fieldModes, rrm.m.Values`fieldModes );
//     //   assert k.fieldModes  == v.fieldModes;
//     //












//////////////////////////////////////////////////////////////////////
//  all junk = 4 MAy 2026
//////////////////////////////////////////////////////////////////////
/// trying to optimise - 26 Feb 2026
//////////////////////////////////////////////////////////////////////
//
//     //  CKV_preconditions
//         assert rm.SuperCalidFragilistic();
//         assert k.Ready();
//         assert rm.ownersInKlown(k);
//         assert rm.o.Ready();
//         assert rm.objectInKlown(rm.o);
//
//            assert k in rm.oHeap;   //CalidCanKey
//            assert k !in rm.m.Keys;
//            assert v !in rm.m.Values;
//         assert rm.CalidCanKey(k);
//         assert NOV: v !in rm.m.Values;
//         assert k in rm.oHeap;
//         assert (v.Ready() && v.Valid() && v.Context(rm.hns({v})));
//         assert rm.m.Keys <= rm.oHeap;
//         assert klonVMapOK(rm.m);
//
//            assert canVMapKV(rm.m, k, v); //klonCanKV
//            assert v != k;
//            assert v !in rm.oHeap;
//            assert (if (v==k) then (v in rm.oHeap) else (v !in rm.oHeap));
//            assert k.Ready() && k.Valid() && k.Context(rm.oHeap);
//            assert v.Ready() && v.Valid() && v.Context(rm.hns({v}));
//            assert rm.ownersInKlown(k);
// //NO_FIELDMODES              assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
// //NO_FIELDMODES              assert v.fieldModes == k.fieldModes;
//         assert klonCanKV(rm, k, v);
//
//         assert k.Ready();    //CalidLineKV preconditions
//         assert rm.ownersInKlown(k);
//         assert v.Ready();
//         assert m.apoCalidse();
//
//                //CalidLineKV
//            assert k in rm.oHeap;
//            assert (not(inside(k,rm.o)) ==> (v == k));
//            assert (   (inside(k,rm.o)) ==> (v !in rm.oHeap));
//            assert (k.AMFX <= rm.m.Keys);
//            assert (k.AMFB <= rm.m.Keys);
//            assert rm.ownersInKlown(k);
//            assert (checkOwnershipOfClone(k,v,rm));
//
//                 //checkBoundOfClone precondition
//                 assert k.Ready();
//                 assert rm.ownersInKlown(k);
//                 assert v.Ready();
//                 assert k.owner <= rm.m.Keys <= rm.oHeap;
//                 assert rm.m.Values <= flatten( rm.hns() );
//                 assert rm.o.Ready();
//                 assert rm.objectInKlown(m.o);
//                 assert rm.HeapOwnersReady();
//  //DAFWONT               assert rm.c_amfx <= rm.oHeap;
//                 //checkBoundOfClone body
//                 assert  ((v == k) || (v.AMFB >=  k.AMFB));     //ERR.
//  //ERR.            assert (checkBoundOfClone(k,v,rm));         //ERR.
//            assert (mappingOwnersThruKlownKV(k,v,rm));
//         assert rm.CalidLineKV(k,v);                            //ERR.?
//         assert rm.OwnersLineKV(k,v);
//
//                 //HighLineKV precondition
//                 assert m.apoCalidse();
//                 //HighLineKV body
//                 assert (k.Ready() && (rm.ownersInKlown(k)) && k in rm.oHeap);
//                 assert (v.Ready() && (v in rm.hns({v})));
//                 assert (v.AMFO  >= v.AMFB  >= k.AMFB);
//                 assert ((inside(k, rm.o)) ==> (k.AMFB  <= rm.o.AMFB));
//                 assert (outside(k, rm.o) <==>  (v == k));
//                 assert ( inside(k, rm.o) <==>  inside(v, rm.m[rm.o]) );
//                 assert ( (k == rm.o)     <==>  (v == rm.m[rm.o])  );
//                 assert ( inside(k, rm.o) <==> (v !in rm.oHeap));
//                 assert (outside(k, rm.m[rm.o]));
// //NO_FIELDMODES                   assert (k.fieldModes   == v.fieldModes);
//                 assert (mappingOwnersThruKlownKV(k,v,rm));
//
//     assert klonReady(m');
//     assert klonCalid(m');
//
//
//
//     assert klonReady(m);
//     assert klonCalid(m);
//    //     assert HighLineKV(k,v,m);
//
// end CKV_preconditions
//////////////////////////////////////////////////////////////////////





















//////////////////////////////////////////////////////////////////////
//  all junk = 4 MAy 2026
//////////////////////////////////////////////////////////////////////

//     //     assert k.owner <        = rm.m.Keys <= rm.oHeap;
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




//////////////////////////////////////////////////////////////////////
//  all junk = 4 MAy 2026
// // //TOUT LES POSTCONDITIONS// //  // //  // //  // //  // //  // //  // //
// {
//
//    var m := rm;
//
//
// //NO_FIELDMODES      assert forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes;
// //NO_FIELDMODES      assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
//    assert m.SuperCalidFragilistic();
//    assert HighCalidFragilistic(m);
//    assert m.from(m');
//    assert m.ownersInKlown(k);
// // assert m.m[k] == v;
// //NO_FIELDMODES      assert k.fieldModes  == v.fieldModes;
//    assert v.Ready() && v.Valid();
//    assert v.Context(m.hns({v}));
//    assert m.CalidLineKV(k,v);
//    assert HighLineKV(k,v,m);
// }
// //  //FIN DES POSTCONDITIONS// //  // //  // //  // //  // //  // //  // //
// //







//////////////////////////////////////////////////////////////////////
//  all junk = 4 MAy 2026
//
//   assert  COK(k,  m'.oHeap);
//   assert  COK(k,  rm.oHeap);
//   assert  COK(k, rm.oHeap);
//
// /////////////////////////////////////////////////////////////// ///////


  assert klonReady(rm);
  assert klonCalid(rm);
  assert rm.ownersReadyInKlown(k);
  assert k  in rm.oHeap;
  assert k !in rm.m.Keys;
  assert v !in rm.m.Values;
  assert klonLine(k,v,rm);
  CKV_PRECONDS(k,v,rm);
  assert rm.CKV_preconditions(k,v);


// //axxume rm.CKV_preconditions(k,v);
   var xm := rm.CalidKV(k,v);
// //////////////////////////////////////////////////////////////////////
//   assert k.fieldModes  == v.fieldModes;
//NO_FIELDMODES  haventFuckedFieldModes(rm,k,v,xm);
//NO_FIELDMODES  FieldModesAreStillOK(k,v,xm,rm);
//
//
//   assert  COK(k,  m'.oHeap);
//   assert  COK(k, rrm.oHeap);
//   assert  COK(k,  xm.oHeap);
//
//
//assert HighLineKV(k, v, xm);

assert klonLine(k,v,xm);
assert klonReady(xm);
assert klonCalid(xm);


//
// //
// // //TOUT LES POSTCONDITIONS// //  // //  // //  // //  // //  // //  // //
// {
//    var m := xm;
// //NO_FIELDMODES      assert forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes;
//  //DAFWONT       assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
//    assert m.SuperCalidFragilistic();
//    assert HighCalidFragilistic(m);   //Err.
//    assert m.from(m');
//    assert m.objectInKlown(k);
//    assert m.m[k] == v;
// //NO_FIELDMODES      assert k.fieldModes  == v.fieldModes;
//    assert v.Ready() && v.Valid();
//    assert v.Context(m.hns());
//    assert m.CalidLineKV(k,v);
//    assert HighLineKV(k,v,m);
// }
// //  //FIN LES POSTCONDITIONS// //  // //  // //  // //  // //  // //  // //
// //
//
//








//
//   //FUCKTODO
//   // assert forall z <- xm.m.Keys :: z.fieldModes == xm.m[z].fieldModes;
//   //   assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
//   //
//   //   assert xm.from(rrm);
//   //
//   //   print "Clone_Clone_Clone map updated ", fmtobj(k), ":=", fmtobj(v) ,"\n";
//   //
//   // assert k in xm.m.Keys;
//   // assert v in xm.m.Values;
//   //
//   //   assert xm.m.Values >= m'.m.Values + {v};
//   //FUCKTODO
//
  XCC_decreases_to_XAF(k,v,xm);
//
// //////////////////////////////////////////////////////////////////////
  assert klonReady(xm);
  assert klonCalid(xm);
  assert xm.objectInKlown(k);
  assert COK(k,xm.oHeap);
  assert v.Context(xm.hns({v}));
  assert inside(k, xm.o);
  assert xm.m[k] == v;
// //////////////////////////////////////////////////////////////////////
// assert COK(k, xm.oHeap);
  m := /*FAKE_*/Xlone_All_Fields(k,v, xm); //this was deleted - who the fuck knows how long for?  //ERR. - likely can't called precondis...


assert klonLine(k,v,m);
assert klonReady(m);
assert klonCalid(m);



//r //////////////////////////////////////////////////////////////////////
// //////////////////////////////////////////////////////////////////////
// //KEYS  assert k.fields.Keys == v.fields.Keys;
//
//   assert  COK(k,  m'.oHeap);
//   assert  COK(k, rrm.oHeap);
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

//// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// ////
//// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// ////
//// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// ////



// //TOUT LES POSTCONDITIONS// //  // //  // //  // //  // //  // //  // //
//NO_FIELDMODES      assert forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes;
//NO_FIELDMODES      assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );

//following is all old - 4 MAy 2026
//    assert m.SuperCalidFragilistic();
//    assert HighCalidFragilistic(m);
//    assert m.from(m');
//    assert m.objectInKlown(k);
//    assert m.m[k] == v;
// //NO_FIELDMODES      assert k.fieldModes  == v.fieldModes;
//    assert v.Ready() && v.Valid();
//    assert v.Context(m.hns());
//    assert m.CalidLineKV(k,v);
//    assert HighLineKV(k,v,m);
// //  //FIN LES POSTCONDITIONS// //  // //  // //  // //  // //  // //  // //
//


assert klonLine(k,v,m);
assert klonReady(m);
assert klonCalid(m);




}//end Clone_Clone_Clone


















lemma IncorporateNewObject(rowner : Owner, rbound : Owner, k : Object, v : Object, m : Klon)
   requires klonReady(m)
   requires klonCalid(m)
   requires m.ownersReadyInKlown(k)
   requires COK(k, m.oHeap)
   requires k in m.oHeap
   requires k !in m.m.Keys
   requires v !in m.m.Values

   requires rowner == v.owner
   requires rbound == v.bound
   requires rowner == mapThruKlon(k.owner, m)
   requires rbound == mapThruKlon(k.bound, m)
  {
      reveal COK();

  }


lemma {:isolate_assertions} BoundsOfCloneOK(k : Object, v : Object, m : Klon)
  //suprious lemma, just use MappedBounds in Klon-Lemmata which does all the work
   requires klonReady(m)
   requires klonCalid(m)
   requires m.ownersReadyInKlown(k)
   requires COK(k, m.oHeap);    requires COKA: COK(k, m.oHeap);
   requires k in m.oHeap
   requires strictlyInside(k, m.o)
   requires strictlyInside(v, m.c)
   requires v.owner == mapThruKlon(k.owner, m)
   requires v.bound == mapThruKlon(k.bound, m)

   ensures myBoundsOK(v.owner, v.bound)
   ensures nuBoundsOK(v.owner, v.bound)
   //ensures klonLine(k,v,m)

  {
      reveal COK();
      assert COK(k, m.oHeap) by { reveal COKA; }
    assert k.Ready();

assert (flatten(k.owner) >= flatten(k.bound));

assert (forall o <- k.owner :: flatten(o.ownerBound()) >= flatten(k.bound));


MappedBounds(k,v,m);

assert (flatten(v.owner) >= flatten(v.bound));

assert (forall o <- v.owner :: flatten(o.ownerBound()) >= flatten(v.bound));

  }
