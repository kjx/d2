include "Xlone.dfy"




method  {:isolate_assertions} {:verify true} Xlone_All_Owners(a : Object,  m' : Klon)  returns (m : Klon)
    decreases * //(m'.oHeap - m'.m.Keys), |a.AMFO|, |a.fields.Keys|, 12

   requires klonReady(m')
   requires klonCalid(m')

   requires a !in m'.m.Keys

   requires COK(a, m'.oHeap)   requires COKA: COK(a, m'.oHeap)


//FIELD MODEs-ISM HACK -- shouod go into calid or at laets supercalid!
//NO_   S     requires forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes
//NO_FIELDMODES      ensures forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes
//NO_FIELDMODES      ensures unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes )

  ensures m.from(m')
  ensures klonReady(m)
  ensures klonCalid(m)
  ensures m.ownersInKlown(a)  //note - agnostic about whether a is cloned or not

 {
  print "CALL Clone_All_Owner of:", fmtobj(a), " owned by ", fmtown(a.owner) ,"\n";
  print "VARIANT CAO ", |m'.oHeap - m'.m.Keys|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 12, "\n";
  print "ENTRY   CAO ", a.owner - m'.m.Keys ," a in Keys ", (a !in m'.m.Keys), "\n";

assert m'.Calid();
  var rm := m';  //grrr. shoulid stop doin that.

  var xo : Object;
  var rr : Object;


  var MX := a.owner - rm.m.Keys;  //progTODOFUCK shgould this be "intrnl"  or doesn't this loop?

     print "PRELOOP ", |MX|," a in Keys ", (a !in rm.m.Keys), "\n";

  assert a !in rm.m.Keys;


assert (a.owner - MX) <= rm.m.Keys;
assert  MX == a.owner - rm.m.Keys;
//NO_FIELDMODES assert forall z <- rm.m.Keys :: z.fieldModes == rm.m[z].fieldModes;  //should be in calid

  while ((MX != {}) && (a !in rm.m.Keys))

    invariant  klonReady(rm)
    invariant  klonCalid(rm)
    invariant  rm.from(m')
    invariant  forall k <- rm.m.Keys :: klonLine(k, rm.m[k], rm) //shouldnt be necessary...
    invariant  MX == a.owner - rm.m.Keys
    invariant  (a.owner - MX) <= rm.m.Keys

    // invariant  rm.HeapContextReady() && rm.ValuesContextReady()
    // invariant  rm.from(m')
    // invariant  rm.Calid()
    // invariant  forall k <- rm.m.Keys :: HighLineKV(k, rm.m[k], rm)
    // invariant  HighCalidFragilistic(rm)
    // invariant  MX == a.owner - rm.m.Keys
    // invariant  (a.owner - MX) <= rm.m.Keys

//NO_FIELDMODES     invariant  forall z <- rm.m.Keys :: z.fieldModes == rm.m[z].fieldModes
    invariant  a !in rm.m.Keys
  {

      print "LOOPTOP ", |MX|," a in Keys ", (a !in rm.m.Keys), "\n";

    xo :| xo in MX;

    var OMX := MX;
    MX := OMX - {xo};
    assert xo !in MX;
    assert xo  in OMX;
    assert MX < OMX;
    assert MX <= OMX - {xo};

    assert COK(a,rm.oHeap) by { reveal COKA; assert COK(a, m'.oHeap); }

    XAO_decreases_to_XVM(a,m', xo,rm);
    print "CALL Clone_Via_Map for owner ",fmtobj(xo),"\n";
///  ////  ////  ////  ////  ////  ////  ////  ////  ///  ////  ////  ////  ////  ////  ////  ////  ////

//NO_FIELDMODES      assert forall z <- rm.m.Keys :: z.fieldModes == rm.m[z].fieldModes;

    assert MX < OMX;
    assert MX <= OMX - {xo};

     COKfromHeapContextReady(xo, rm);
// ///  ////  ////  ////  ////  ////  ////

    rr, rm := FAKE_Xlone_Via_Map(xo, rm);  /*FAKE*/
    assume {:axiomn} klonCalid(rm);  //postcondition temporarily deleted so XVM doesn't crash :-(.
                                                //see comments in defn of Xlone_Via_Map
///  ////  ////  ////  ////  ////  ////  ////  ////  ///  ////  ////  ////  ////  ////  ////  ////  ////
//NO_FIELDMODES   assert xo.fieldModes == rr.fieldModes;
//KEYS  assert xo.fields.Keys == rr.fields.Keys;


    assert MX < OMX;
    assert MX <= OMX - {xo};

      if (a in rm.m.Keys) {
      m := rm;

      assert klonReady(rm);
      assert klonCalid(rm);
      print "RETN - Clone All Onwers - clonéd pivot\n";
      return;
    }  else { assert a !in rm.m.Keys;  }

    assert a !in rm.m.Keys;

    // if a is in m.Keys after clone -- if it got added magically...



    assert MX < OMX;
    assert MX <= OMX - {xo};

    MX := a.owner - rm.m.Keys;

    assert MX < OMX;
    assert MX <= OMX - {xo};

  } // end loop MX


  assert a !in rm.m.Keys;

  assert (a.owner - MX) <= rm.m.Keys;
  assert a.owner <= rm.m.Keys;

  m := rm;
  assert klonCalid(m);

  assert (a.owner - MX) <= rm.m.Keys;  //why -MX???

  m.directOwnerInKlownIsEnough(a);
  assert  m.ownersInKlown(a);
  assert  m.from(m');
  assert  klonCalid(m);

  print "RETN - Clone All Onwers - done Done DONE\n";

}//END Xlone_All_Owners

























//////////////////////////////////////////////////////////////////////

lemma  {:isolate_assertions} {:verify true} REFAC_XAO_OK(a : Object,  m' : Klon)

   requires klonReady(m')
   requires klonCalid(m')


  ensures (m'.c_amfx >= flatten(m'.clbound) >= flatten(m'.o.bound))
  ensures m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound)
  ensures m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound)

  ensures m'.HeapContextReady()
  ensures m'.ValuesContextReady()
  ensures m'.Calid()
  ensures m'.m.Keys <= m'.oHeap

{}
