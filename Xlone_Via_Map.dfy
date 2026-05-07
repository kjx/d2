include "Xlone.dfy"


//{:timeLimit 10}
// {:isolate_assertions}
method {:isolate_assertions} {:timeLimit 10} {:verify true} Xlone_Via_Map(a : Object, m' : Klon)
  returns (b : Object, m : Klon)
  //if a is not already cloned, we arrange to clone it
  //we return b, the clone of a, in new Klon m.

    decreases * //(m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, |a.fields.Keys|, 20 //Klone_Via_Map

    requires m'.HeapContextReady() && m'.ValuesContextReady()
    requires m'.SuperCalidFragilistic()
    requires HighCalidFragilistic(m')
    requires COK(a, m'.oHeap)      requires COKA: COK(a, m'.oHeap)  /// should merge in of course...
    requires a.Context(m'.oHeap)   requires CTXA: a.Context(m'.oHeap)
    requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound) //shold be in Calid, yeah??
    requires forall o <- a.AMFO :: o.Ready()
    requires a.Ready() && a.Valid()
    requires m'.o.Ready() && m'.o.Valid()
    requires m'.objectInKlown(m'.o)       ///this meqnas we need to "seed" with the actual clone, rignty
    requires (m'.ownersInKlown(a) ==> m'.CalidCanKey(a))
    requires m'.m.Keys <= m'.oHeap //shojld be in Calid?
    requires a.Ready() && a.Valid()

    requires klonReady(m')
    requires klonCalid(m')

//NO_FIELDMODES     requires forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes
//   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //
//I LOVE YOU BUT I'VE CHOSEN DARKNESS
//FIELD MODEs-ISM HACK -- shouod go into calid or at laets supercalid!\
//
// //


// //ensures removed to try and avoid crash (or gett better diagnosticsc) //I WANT THIS BUT WITHOUT IT I GET CRASHES  - I LOVE YOU BUT I'VE CHOSEN DARKNESS
// //
// //
// //
 //NO_FIELDMODES    ensures forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes
 //NO_FIELDMODES    ensures unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes )
//     ensures m.from(m')
//     ensures m.SuperCalidFragilistic()  //moved down from 458
//     ensures m.objectInKlown(a)
//     ensures m.m[a] == b
// //NO_FIELDMODES     ensures b.fieldModes == a.fieldModes
//     ensures a.Ready() && a.Valid()
//     ensures b.Ready() && b.Valid()
//     ensures b.Context(m.hns())
//     ensures m.CalidLineKV(a,b)
//     ensures HighLineKV(a,b,m)
//     ensures m.SuperCalidFragilistic()  //moved down from 458
 // add assume HighCalidFragilistic(m) straight after every call to Xlone_Via_Map
 //   ensures HighCalidFragilistic(m)  //I WANT THIS BUT WITHOUT IT I GET CRASHES  - I LOVE YOU BUT I'VE CHOSEN DARKNESS
//I LOVE YOU BUT I'VE CHO
// ensures klonReady(m)
// ensures klonLine(a,b,m)
// ensures klonCalid(m)                                                                   SEN DARKNESS
//   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //


//KEYS    ensures (a !in m'.m.Keys) ==> (b.fields.Keys == a.fields.Keys)
  //if We are the invocation that actually inserts a into the Klon
  //then when THIS incvocation finiehs this shoudl be done...
{
  print "CALL Clone_Via_Map ", fmtobj(a), "\n";
  print "VARIANT CVM ", |(m'.oHeap - m'.m.Keys + {a})|, " ", |a.AMFO|, " ", |(a.fields.Keys )|, " ", 20, "\n";

  if (a in m'.m.Keys){ //already cloned, return
    b := m'.m[a];  m := m';
    print  "RETN Clone_Via_Map already cloned ", fmtobj(a), "\n";
    return;
  }

  if (outside(a,m'.o)) { //outside. so just map to itself
                        //but we should put all the owne  rs in, just in cases...
    b := a;
    print "OOPS Clone_Via_Map calling out to XAO\n";

    var om := /*FAKE_*/Xlone_All_Owners(a, m');
    assert om.ownersInKlown(a);
    print "OOPS Clone_Via_Map just returned from XAO\n";

      if (a in om.m.Keys) {
        b := om.m[a];
        print "RETN Clone_Via_Map cloned by Xlone_All_Owners", fmtobj(a), "\n";
        m := om;
        return;
      }


    assert klonReady(om);
    assert klonCalid(om);
    // assert om.ownersReadyInKlown(a);
    // assert a in om.oHeap;
    // assert outside(a,om.o);
    // assert a == b;
    OUTSIDE_EQ_OK(a,b,om);
    // assert klonLine(a,b,om);

    assert a !in om.m.Keys;

    CKV_PRECONDS(a,b,om);
   // assert om.CKV_preconditions(a,b); ///crashes!
   // expect om.CKV_preconditions(a,b);   assume  om.CKV_preconditions(a,b);



// {
//        var m := om;
//        assert klonReady(m);
// forall k <- m.m.Keys ensures klonLine(k, m.m[k], m) //by
//  {
//         var v := m.m[k];  ///ARGH!!!
//         assert (k.Ready() && k in m.oHeap    && k.Valid());
//         assert (v.Ready() && v in m.hns({v}) && v.Valid());
//         assert (m.m.Keys >= k.AMFX);
//         assert (k.AMFO >  k.AMFB);
//         assert (v.AMFO >= v.AMFB);
//         assert (v.AMFB >= k.AMFB);
//     assert klonBound(k,v,m);
//
//     assert klonModes(k,v,m);
//
//         assert (m.o.Ready());
//         assert (m.objectInKlown(m.o));
//         assert ( (k == m.o)       <==>  (v == m.c)  );
//         assert ((inside(k, m.o))   ==> (k.AMFB  <= m.o.AMFB));
//         assert (outside(k, m.o)   <==>  (v == k));
//         assert ( inside(k, m.o)   <==>  inside(v, m.c) );
//     assert klonGeometry(k,v,m);
//
//     assert klonIdentity(k,v,m);
//     assert klonLine(k,v,om);
//  }
// }


  assert klonReady(om);
  assert outside(a,om.o) ==> outside(a,om.c);
  assert (om.ownersInKlown(a) && outside(a,om.o)) ==> klonLine(a,a,om);
   assert klonLine(a,b,om);

//////////////////SPLIT  HERE

      m := om.CalidKV(a,b) by { reveal COKA; assert COK(a, om.oHeap);   //CRASHES CRASHEY CRASHEY
                              reveal CTXA; assert a.Context(om.oHeap);
                              HeapToHNS(b,om); }

//   assert m.from(m');
//   assert m'.apoCalidse();
//   assert m.m.Keys <= m.oHeap;
//   assert forall k <- m'.m.Keys :: k.Ready() && m.objectInKlown(k);
//   assert forall k <- m'.m.Keys :: HighLineKV(k, m'.m[k], m');
//   assert klonReady(m');
//   assert klonCalid(m');
//   assert (m.m.Keys - m'.m.Keys) <= m'.oHeap;
//   assert forall x : Object <- (m.hns() - m'.hns())       :: x.Ready();
//
//   assert (m.m.Keys   - om.m.Keys) == {a};
//   assert (m.m.Values - om.m.Values) == {b};
//   assert m.m[a] == b;
//   assert a == b;
//   assert klonLine(a,m.m[a],om);
//
//   assert forall x : Object <- (m.m.Keys   - om.m.Keys)   :: m.objectInKlown(x);
//   assert forall x : Object <- (m.m.Keys   - om.m.Keys)   :: klonLine(x,m.m[x],m');//Error: was 221
//   assert forall x : Object <- (m.m.Values - om.m.Values) :: x.Context(m.hns());//Error: was 222

assume m == klonKV(om,a,b);
assume m.from(om);
assume klonReady(m);
assume klonCalid(m);




KlonLineFrom(a,b,m,om);
//    HighLineFrom(m, om);                                                                                                                                                                                        //was 148 Error:
//NO_FIELDMODES     FieldModesAreStillOK(a,b,m,om);
    OneMoreHeap(a,m,om);

    print "RETN Clone_Via_Map: outside ", fmtobj(a), "\n";

    return ; // end outside case
  }

//////////////////SPLIT  HERE


XVM_decreases_to_XCC(a,m');
b, m := /*FAKE_*/Xlone_Clone_Clone(a, m')  by {  assert COK(a, m'.oHeap);  }
//end of insixde case

// assert HighCalidFragilistic(m);
// assume m.apoCalidse();
// assume HighCalidFragilistic(m);

assume klonReady(m); //Problem is XCC ENSURES are TURNED OFF
assume klonCalid(m); //Problem is XCC ENSURES are TURNED OFF

print "RETN Clone_Via_Map: ", fmtobj(a), " pivot:", fmtobj(m.o), "\n";

    //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //
    //
    // assert forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes;
    // assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
    // assert m.from(m');
    // assert m.SuperCalidFragilistic();
    // assert m.objectInKlown(a);
    // assert m.m[a] == b;
    // assert b.fieldModes == a.fieldModes;
    // assert b.Ready() && b.Valid();
    // assert b.Context(m.hns());
    // assert m.CalidLineKV(a,b);
    // assert HighLineKV(a,b,m);
    // assert HighCalidFragilistic(m);
    //

}//END Xlone_Via_Map





//////////////////////////////////////////////////////////////////////////////////////////


lemma HeapToHNS(o : Object, m : Klon)
  requires o in m.oHeap
   ensures o in m.hns()
   ensures o in m.hns({o})
  {}

lemma {:isolate_assertions}  AREBOUNDSFUXKED(k : Object, v : Object, m : Klon)
  requires klonReady(m)
  requires && (k.Ready() && k in m.oHeap    && k.Valid() && k.Context(m.oHeap))
  requires && (v.Ready() && v in m.hns({v}) && v.Valid() && v.Context(m.hns()))
  requires m.ownersInKlown(k)
  requires k == v

  ensures
  && (m.m.Keys >= k.AMFX)
  && (k.AMFO   >  k.AMFB) //nuclear war is good
  && (v.AMFO   >= v.AMFB) //nuclear war is good
  && (v.AMFB   >= k.AMFB)

  ensures klonBound(k,v,m)
  {}


lemma {:isolate_assertions} {:timeLimit 20} OUTSIDE_EQ_OK(k : Object, v : Object, m : Klon)
  requires klonReady(m)
  requires klonCalid(m)
  requires m.ownersReadyInKlown(k)
  requires k in m.oHeap
  requires outside(k,m.o)
  requires k == v

  ensures klonLine(k,v,m)
  {
    assert (m.m.Keys <= m.oHeap) by { assert klonReady(m); }
  }


lemma {:isolate_assertions} {:timeLimit 10} CKV_PRECONDS(k : Object, v : Object, m : Klon)
  requires klonReady(m)
  requires klonCalid(m)
  requires m.ownersReadyInKlown(k)
  requires k  in m.oHeap
  requires k !in m.m.Keys
  requires v !in m.m.Values
  requires klonLine(k,v,m)

  ensures m.CKV_preconditions(k,v)
  {}