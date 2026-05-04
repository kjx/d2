



method  {:isolate_assertions} {:verify true} Xlone_All_Owners(a : Object,  m' : Klon)  returns (m : Klon)
    decreases * //(m'.oHeap - m'.m.Keys), |a.AMFO|, |a.fields.Keys|, 12

   requires klonReady(m')
   requires klonCalid(m')

  requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound)
  requires a !in m'.m.Keys
//  requires inside(a, m'.o)


//START FROM XVM
  requires m'.HeapContextReady() && m'.ValuesContextReady() &&  m'.Calid()
  requires m'.SuperCalidFragilistic()
  requires HighCalidFragilistic(m') //TUESDAY

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
//NO_   S     requires forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes
//NO_FIELDMODES      ensures forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes
//NO_FIELDMODES      ensures unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes )

  ensures  m.from(m')
  ensures  m.SuperCalidFragilistic()
  ensures  m.ownersInKlown(a)
  ensures  HighCalidFragilistic(m) //TUESDAY


  ensures klonReady(m)
  ensures klonCalid(m)

// ensures  a !in m.m.Keys  NOT THIS ONE PROBABLU SHOULDN"T HOLD.

 {
  print "CALL Clone_All_Owner of:", fmtobj(a), " owned by ", fmtown(a.owner) ,"\n";
  print "VARIANT CAO ", |m'.oHeap - m'.m.Keys|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 12, "\n";
  print "ENTRY   CAO ", a.owner - m'.m.Keys ," a in Keys ", (a !in m'.m.Keys), "\n";

assert m'.Calid();
  var rm := m';  //grrr. shoulid stop doin that.

//  assert HighCalidFragilistic(rm);
//   assert rm.from(m');
//   assert rm.Calid();
//   assert COK(a,rm.oHeap) by { reveal COKA; assert COK(a,m'.oHeap); assert COK(a,rm.oHeap); }
//
  var xo : Object;
  var rr : Object;
  // var oldmks  : set<Object>;  //dont fucking ask
  // var oldmok :=  false;

  var MX := a.owner - rm.m.Keys;  //progTODOFUCK shgould this be "intrnl"  or doesn't this loop?

     print "PRELOOP ", |MX|," a in Keys ", (a !in rm.m.Keys), "\n";

  assert a !in rm.m.Keys;
  //assert not(a.AMFX <= rm.m.Keys);

// assert rm.Calid();
// assert HighCalidFragilistic(rm);
// assert forall k <- rm.m.Keys :: HighLineKV(k, rm.m[k], rm);

assert klonReady(rm);
assert klonCalid(rm);
assert klonAllLines(rm);
assert forall x <- rm.m.Keys :: klonLine(x, rm.m[x], rm);

assert (a.owner - MX) <= rm.m.Keys;
assert  MX == a.owner - rm.m.Keys;
//NO_FIELDMODES assert forall z <- rm.m.Keys :: z.fieldModes == rm.m[z].fieldModes;  //should be in calid

  while ((MX != {}) && (a !in rm.m.Keys))

    invariant  rm.HeapContextReady() && rm.ValuesContextReady()
    invariant  rm.from(m')
    invariant  rm.Calid()
    invariant  forall k <- rm.m.Keys :: HighLineKV(k, rm.m[k], rm)
    invariant  HighCalidFragilistic(rm)
    invariant  MX == a.owner - rm.m.Keys
    invariant  (a.owner - MX) <= rm.m.Keys

//NO_FIELDMODES     invariant  forall z <- rm.m.Keys :: z.fieldModes == rm.m[z].fieldModes
    invariant  a !in rm.m.Keys
  {

      print "LOOPTOP ", |MX|," a in Keys ", (a !in rm.m.Keys), "\n";

    xo :| xo in MX;

// NO_CODE OR SOMELTRB*IN G
//     assert M   X == a.owner - rm.m.Keys;
//     assert xo in (a.owner - rm.m.Keys);
//     assert xo in a.owner;
//     assert xo !in rm.m.Keys;
//
    var OMX := MX;
    MX := OMX - {xo};
    assert xo !in MX;
    assert xo  in OMX;
    assert MX < OMX;
    assert MX <= OMX - {xo};
//
//   assert a.AMFO > xo.AMFO;
//   assert rm.from(m');
//   assert xo in (a.owner - rm.m.Keys);
//   assert a in rm.oHeap;

    assert COK(a,rm.oHeap) by { reveal COKA; assert COK(a, m'.oHeap); }

    XAO_decreases_to_XVM(a,m', xo,rm);
    print "CALL Clone_Via_Map for owner ",fmtobj(xo),"\n";
///  ////  ////  ////  ////  ////  ////  ////  ////  ///  ////  ////  ////  ////  ////  ////  ////  ////
///NO_CODE
    //  assert rm.HeapContextReady() && rm.ValuesContextReady();
    //  assert rm.SuperCalidFragilistic();
    //  assert HighCalidFragilistic(rm); //TUESDAY
    //  assert rm.oHeap >= flatten(rm.clowner) >= flatten(rm.clbound);
    //  assert forall o <- a.AMFO :: o.Ready();
    //  assert a.Ready() && a.Valid();
    //  assert rm.o.Ready() && rm.o.Valid();
    //  assert rm.objectInKlown(rm.o);
    //  assert (rm.ownersInKlown(a) ==> rm.CalidCanKey(a));
    //  assert rm.m.Keys <= rm.oHeap ;
    //  assert a.Ready() && a.Valid();
//NO_FIELDMODES      assert forall z <- rm.m.Keys :: z.fieldModes == rm.m[z].fieldModes;

    assert MX < OMX;
    assert MX <= OMX - {xo};

     COKfromHeapContextReady(xo, rm);
//     assert HighCalidFragilistic(rm);   //TUESDAY
// ///  ////  ////  ////  ////  ////  ////

    rr, rm := FAKE_Xlone_Via_Map(xo, rm);  /*FAKE*/
    assume {:axiomn} HighCalidFragilistic(rm);  //postcondition temporarily deleted so XVM doesn't crash :-(.
                                                //see comments in defn of Xlone_Via_Map
///  ////  ////  ////  ////  ////  ////  ////  ////  ///  ////  ////  ////  ////  ////  ////  ////  ////
  //NO_CODE
  //   assert rm.from(m');
  // assert xo in rm.m.Keys;
  // assert xo !in (a.owner - rm.m.Keys);
//NO_FIELDMODES   assert xo.fieldModes == rr.fieldModes;
//KEYS  assert xo.fields.Keys == rr.fields.Keys;
  // assert HighCalidFragilistic(rm); //TUESDAY
  // assert rr.Ready() && rr.Valid();
  // assert rr.Context(rm.hns());

    assert MX < OMX;
    assert MX <= OMX - {xo};

      if (a in rm.m.Keys) {
      m := rm;
      //NO_CODE
      // assert m.from(m');
      // assert (forall z <- m.m.Keys ::  (m.objectInKlown(z)));
      // assert  m.ownersInKlown(a);
      // assert  m.SuperCalidFragilistic();
      assert HighCalidFragilistic(rm); //TUESDAY
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

    // oldmks := rm.m.Keys;
    // oldmok := true;
    rm := rm; //whaaat?
  } // end loop MX


  assert a !in rm.m.Keys;

  assert (a.owner - MX) <= rm.m.Keys;
  assert a.owner <= rm.m.Keys;

  assert rm.Calid();
  assert HighCalidFragilistic(rm); //TUESDAY

  m := rm;
  assert m.Calid();

  // if (a in rm.m.Keys) {
  //   assert (forall z <- m.m.Keys ::  (m.objectInKlown(z)));
  //   assert  m.ownersInKlown(a);
  //   assert  m.from(m');
  //   assert  m.SuperCalidFragilistic();
  //   return;
  // }

  //else
  assert (a.owner - MX) <= rm.m.Keys;  //why -MX???

  m.directOwnerInKlownIsEnough(a);
  assert  m.ownersInKlown(a);
  assert  m.from(m');
  assert  m.SuperCalidFragilistic();

  assert (forall k <- m.m.Keys :: HighLineKV(k, m.m[k], m));
  assert HighCalidFragilistic(m); //TUESDAY

  print "RETN - Clone All Onwers - done Done DONE\n";

}//END Xlone_All_Owners
