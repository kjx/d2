include "Xlone.dfy"






//  {:timeLimit 300} --- real	17m50.852s 09 April
method {:isolate_assertions} {:timeLimit 300} {:verify true} Xlone_Field_Map(a : Object, n : string, b : Object, m' : Klon)
  returns (m : Klon)
  //given b is an structural clone of a (m.m[a]==b)
  //create a new b.n == cloneOf a.n (m.m[a.n]) and intsall it in b (via Xlone_Set_Field)

  decreases * //(m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, fielddiff(a,b), 5 //Xlone_Field_Map

  requires b != a
  requires a.Ready()                 requires AIR: a.Ready()
  requires a in m'.m.Keys
  requires m'.m[a] == b              requires MAB: m'.m[a] == b
  requires m'.apoCalidse()
  requires HighLineKV(a,b,m')        requires HIL: HighLineKV(a,b,m')
  requires m'.objectInKlown(a)       requires AIK: m'.objectInKlown(a)

//prog inside
  requires strictlyInside(a, m'.o)    requires AMI: strictlyInside(a, m'.o)
//prog inside

  requires a.Ready() && a.Valid()

  requires n  in a.fields.Keys        requires N_IN_A: n in a.fields.Keys
  requires n !in b.fields.Keys
//NO_FIELDMODES   requires a.fieldModes.Keys == b.fieldModes.Keys
  requires b.Ready() && b.Valid()
  requires a.fields.Keys > b.fields.Keys

  //our only callsite is from Xlone_Via_Map
  // (and could be reintergrated, who knows?)

//NUKEM
//   requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound)
//   requires HOB:  m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound)
//   requires (m'.c_amfx >= flatten(m'.clbound) >= flatten(m'.o.bound))

  //START FROM XVM
  requires m'.SuperCalidFragilistic() //hmm
  requires HighCalidFragilistic(m') //5 Feb 2026- hmm.
  requires HCFm': HighCalidFragilistic(m') //5 Feb 2026- hmm.


  requires COKA: COK(a, m'.oHeap)

  //surely much of the following comes down from Calid()?
  requires m'.o.Ready() && m'.o.Valid()
  requires m'.objectInKlown(m'.o)
  //requires m'.CalidCanKey(a) err & WRONG - a must already be in the thing

  requires a  in m'.oHeap
  requires b !in m'.oHeap
  requires b  in m'.hns()
//NO_FIELDMODES   requires a.fieldModes.Keys == b.fieldModes.Keys
//NO_FIELDMODES   requires n  in b.fieldModes.Keys

  requires m'.m.Keys <= m'.oHeap
  requires allocated(m'.oHeap)
//END FROM XV

//FIELD MODEs-ISM HACK -- shouod go into calid or at laets supercalid!
//NO_FIELDMODES   requires forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes
  // ensures forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes//**17Sep*/
  // ensures forall z <- m'.m.Keys | z != b :: unchanged(z) //**17Feb2026 */
//NO_FIELDMODES   ensures unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes )

  //FRAE HERE
  //   ensures  m.from(m')
  //   ensures  m.SuperCalidFragilistic()  //**17Sep*/
  //   ensures  m.apoCalidse() //**17Feb 2026*/
  //   ensures  HighCalidFragilistic(m) //**7feb2026 */  //TUESDAY
  //   ensures  m.ownersInKlown(a)
  //   ensures  a in m.m.Keys
  //   ensures  n in a.fields.Keys
  //   ensures  unchanged(a`fields)
  //   ensures  n in b.fields.Keys
  //   ensures  b.fields.Keys == old(b.fields.Keys) + {n}
  //   ensures  old(fielddiff(a,b)) decreases to fielddiff(a,b)
  //   ensures  m.m[a] == b
  //   ensures  m.objectInKlown(a.fields[n])
  //   ensures  m.m[ a.fields[n] ] == b.fields[n]
  //   ensures  m.m[ a.fields[n] ] == m.m[a].fields[n]  //prog THIS IS THE KEY POSTCONDITION!!
  // //NO_FIELDMODES   ensures  a.fieldModes.Keys == b.fieldModes.Keys
  //
  // //NO_FIELDMODES   ensures forall z <- m'.m.Keys :: z.fieldModes == old(z.fieldModes) == m'.m[z].fieldModes
  // //NO_FIELDMODES   ensures forall z <- m.m.Keys  :: z.fieldModes == m.m[z].fieldModes
  //
  //   ensures unchanged( m'.oHeap )
  //   ensures unchanged( m.oHeap  )
  //   ensures unchanged( m.oHeap`fields )
  //   ensures allocated( m'.oHeap )
  //   ensures allocated( m.oHeap  )
  //   ensures unchanged( m'.oHeap`fields )
  // //NO_FIELDMODES   ensures unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes )
  //
  //   ensures m.oHeap == m'.oHeap
  //TAE HERE

  modifies b`fields
{
//NO_FIELDMODES   assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
  assert a.fields.Keys > b.fields.Keys;

  print "CALL Clone_Field_Map ", fmtobj(a), ".", n, " to ", fmtobj(b), "\n";
  // assert a != b by {
  //     assert a  in m'.oHeap;
  //     assert b !in m'.oHeap;
  // }
//NO_FIELDMODES   assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
  assert SCFL: m'.SuperCalidFragilistic();
//NO_FIELDMODES   assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
  assert m'.Calid(); assert m'.AllLinesCalid(); assert forall k <- m'.m.Keys :: m'.CalidLineKV(k, m'.m[k]);
  //progTODOFUCK print "CALL Clone_Field_Map ", fmtobj(a), " «", n, "»\n";
  //progTODOFUCK print "VARIANT CFM ", |m'.oHeap - m'.m.Keys + {a}|, " ", |a.AMFO|, " ", fielddiff(a,b), " ", 5, "\n";

  var v_cfm := ((m'.oHeap - m'.m.Keys + {a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Xlone_Field_Map *vxriant for dxcreases clause*

  var onb := m'.ns() - {b};
  var ctx := (m'.oHeap+m'.ns());

  var afK := a.fields.Keys;  var bfK := b.fields.Keys;  var ofd := fielddiff(a,b);
  assert fielddiff(a,b) == |a.fields.Keys - b.fields.Keys| == |afK - bfK| == old(fielddiff(a,b)) == ofd;
  assert n in a.fields.Keys;   assert n in afK; assert n !in bfK;
  TieMeKangaDown(afK,bfK,n);

  var ofv := a.fields[n];
  m'.FieldFromHeapContext(a, n, ofv);
  assert OFV: ofv.Ready() && ofv.Valid() && ofv.Context(m'.oHeap);


//NO_FIELDMODES   assert unchanged( m'.oHeap`fieldModes, m'.m.Values`as );
  assert forall z <- m'.m.Keys | z != b :: unchanged(z);
  assert  b.fields.Keys == old(b.fields.Keys);

  var rfv : Object;
//skipping... if(false){
  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //


  if (ofv in m'.m.Keys)
    {
          rfv := m'.m[ofv];
          m := m';

        assert m.SuperCalidFragilistic();                  assert m.from(m');
        assert HighCalidFragilistic(m);
        assert a.Ready();    assert m.objectInKlown(a);    assert b == m.m[a];
        assert ofv.Ready();  assert m.objectInKlown(ofv);  assert rfv == m.m[ofv];
//NO_FIELDMODES         assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
        assert  b.fields.Keys == old(b.fields.Keys);
        assert  a.fields.Keys == old(a.fields.Keys);

//much of this should be in CalidLineKV...?
        assert ofv.Ready();
        assert rfv.Ready();
        assert m.objectInKlown(ofv);
        assert m.m[ofv] == rfv;
        assert m.CalidLineKV(ofv,rfv);
        assert HighLineKV(ofv,rfv,m);
//NO_FIELDMODES         assert ofv.fieldModes == rfv.fieldModes;

    }
    else

    {
          assert ofv !in m'.m.Keys;
          assert ofv  in m'.oHeap; //cos it's old
          assert a    in m'.m.Keys;
          assert ofv != a;  //ae3 we sure about that? -- yep, cos a *is* in m'.m.Keys...

          assert m'.m.Keys <= m'.oHeap;

        // WHY are we doing this?  do we need to do this?
        //   assert a    in m'.m.Keys;
        //   assert a    in m'.oHeap;
        //   assert a   !in (m'.oHeap - m'.m.Keys);
        //   assert a    in (m'.oHeap - m'.m.Keys + {a});
        //   assert a   !in (m'.oHeap - m'.m.Keys + {ofv});
        //
        //   assert ofv !in m'.m.Keys;
        //   assert OFV_NOTIN: ofv !in m'.m.Keys;
        //   assert ofv  in m'.oHeap;
        //   assert ofv  in (m'.oHeap - m'.m.Keys);
        //   assert ofv  in (m'.oHeap - m'.m.Keys + {a});
        //   assert ofv  in (m'.oHeap - m'.m.Keys + {ofv});

          DownInSplendor((m'.oHeap - m'.m.Keys), a, ofv);
          assert ((m'.oHeap - m'.m.Keys) + {a} decreases to (m'.oHeap - m'.m.Keys)  + {ofv});

          assert (
            ((m'.oHeap - m'.m.Keys) + {a}),   |a.AMFO|,    fielddiff(a,b), 5 //Xlone_Field_Map
            decreases to
            ((m'.oHeap - m'.m.Keys) + {ofv}), |ofv.AMFO|, |ofv.fields.Keys|, 20);

assert COK(a, m'.oHeap) by { reveal COKA; assert COK(a, m'.oHeap); }
assert COK(ofv,m'.oHeap) by {
    reveal COKA; assert COK(a, m'.oHeap);
    CallOKfromHeapContextReady(m');
    assert ofv == COKat(a,  n, m'.oHeap);
    assert  COK(ofv,m'.oHeap); }
reveal COK();  assert a.Ready(); assert a.Valid();
          XFM_decreases_to_XVM(a,b,ofv,m');


//NUKEM assert m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound) by { reveal HOB; }   ///NESTS
//NO_FIELDMODES           assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
  assert afK == a.fields.Keys;
        // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
        // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
////XVM preconditions
  assert m'.HeapContextReady();
  assert m'.ValuesContextReady();
  assert m'.SuperCalidFragilistic();
  assert HighCalidFragilistic(m');
  assert COK(ofv, m'.oHeap);
  assert m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound);
  assert forall o <- ofv.AMFO :: o.Ready();
  assert ofv.Ready();
  assert ofv.Valid();
  assert m'.o.Ready() && m'.o.Valid();
  assert m'.objectInKlown(m'.o);
  assert (m'.ownersInKlown(ofv) ==> m'.CalidCanKey(ofv));
  assert m'.m.Keys <= m'.oHeap;
  assert a.Ready() && a.Valid();
//NO_FIELDMODES   assert forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes;
        // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
        // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
          rfv, m := FAKE_Xlone_Via_Map(ofv, m');   assert m.m[ofv] == rfv; /*FAKE*/
//      assume m.from(m');   assume klonReady(m); assume klonCalid(m);   assume HighCalidFragilistic(m);   assume m.objectInKlown(ofv); // while XVM is switched off...
      assert m.from(m');   assert klonReady(m); assert klonCalid(m);   assert HighCalidFragilistic(m);   assert m.objectInKlown(ofv); // while XVM is switched off...
  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
        // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
    assert afK == a.fields.Keys;
          assert rfv == m.m[ofv];
          assert ofv in m.m.Keys;
    assert rfv.Context(m.hns());
    assert m.CalidLineKV(ofv,rfv);
    assert HighLineKV(ofv,rfv,m);
    assert m.from(m');
    assert HighCalidFragilistic(m);
    assert (forall k <- m.m.Keys :: HighLineKV(k, m.m[k], m));

        assert ofv.Ready();
        assert rfv.Ready();
        assert m.objectInKlown(ofv);
        assert m.m[ofv] == rfv;
  //NO_FIELDMODES         assert ofv.fieldModes == rfv.fieldModes;

    assert m.SuperCalidFragilistic();                  assert m.from(m');
    assert HighCalidFragilistic(m);
    assert a.Ready();    assert m.objectInKlown(a);    assert b == m.m[a];
    assert ofv.Ready();  assert m.objectInKlown(ofv);  assert rfv == m.m[ofv];
//NO_FIELDMODES     assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
    assert  b.fields.Keys == old(b.fields.Keys);
        //from below
        assert ofv.Ready();
        assert rfv.Ready();
        assert m.objectInKlown(ofv);
        assert m.m[ofv] == rfv;
        assert m.CalidLineKV(ofv,rfv);
        assert HighLineKV(ofv,rfv,m);
  } //end else
// end skipping }


  //not sure we need ANY of this - let's seee - 5Feb 2026
  //   assert afK == a.fields.Keys;
  // //this ithereaily jtwi4;>? k     /k       m/m / md
  //   assert forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes;
  //   assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
  //   assert  b.fields.Keys == old(b.fields.Keys);
  //   assert m.SuperCalidFragilistic();                  assert m.from(m');
  //   assert HighCalidFragilistic(m);
  //   assert a.Ready();    assert m.objectInKlown(a);    assert b == m.m[a];
  //   assert ofv.Ready();  assert m.objectInKlown(ofv);  assert rfv == m.m[ofv];

//much of this should be in CalidLineKV...?
        assert ofv.Ready();
        assert rfv.Ready();
        assert m.objectInKlown(ofv);
        assert m.m[ofv] == rfv;
        assert m.CalidLineKV(ofv,rfv);
        assert HighLineKV(ofv,rfv,m);
//NO_FIELDMODES         assert ofv.fieldModes == rfv.fieldModes;   assert oFMrFM: ofv.fieldModes == rfv.fieldModes;


        assert a.Ready() by { reveal AIR; assert a.Ready(); }
//prog inside
    assert strictlyInside(a, m'.o) by { reveal AMI; assert strictlyInside(a, m'.o); }
    assert m.from(m');
    assert strictlyInside(a, m.o);      assert AMO: strictlyInside(a, m.o);
//prog inside
//NO_FIELDMODES         assert ofv.fieldModes == rfv.fieldModes by { reveal oFMrFM; }

///  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /
///
/// at this point, rfv is the requisite field value (or resulting field value or something)
/// either after calling clone, or picking it up as preexistin
/// the rfv (i.e clone field value) should be registered in the Klon against the ofv..
///
/// now we just need to assign the field.
/// could  possible break here make another method.
///
///  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /  /

  m := m'; return; //LINE_BY_FUCKING_LINE

////proof break
{
  var k := a;
  var v := b;
  var t := ofv;
  var u := rfv;

//NO_FIELDMODES    assert ofv.fieldModes.Keys == rfv.fieldModes.Keys by { reveal oFMrFM; }
   assert t == ofv; assert u == rfv;
//NO_FIELDMODES    assert   t.fieldModes.Keys ==   u.fieldModes.Keys by { reveal oFMrFM; }

//Xlone_Set_Field - precondition
   assert v.Valid();
   assert v.OwnersWithin(m.hns({u}));
   assert n !in v.fields;
//NO_FIELDMODES    assert n  in v.fieldModes.Keys;
//NO_FIELDMODES    assert k.fieldModes.Keys == v.fieldModes.Keys;
   assert m.SuperCalidFragilistic();
   assert HighCalidFragilistic(m);
   OwnersFromCalid(m);
   assert m.CalidOwners();
   assert k.Ready() by { reveal AIR;
                          assert a.Ready();
                          assert k.Ready(); }
   assert m.objectInKlown(a) by { reveal AIK;
                            assert m.objectInKlown(a);
                            assert m.objectInKlown(k); }
   assert m.objectInKlown(k) by { reveal AIK; }
   assert m.m[k] == v by { reveal MAB;  }

   assert t.Ready();
   assert m.objectInKlown(t);
   assert m.m[t] == u;
   assert m.CalidLineKV(t,u);         assert HighLineKV(t,u,m);

//NO_FIELDMODES    assert ofv.fieldModes.Keys == rfv.fieldModes.Keys by { reveal oFMrFM; }
   assert t == ofv; assert u == rfv;
//NO_FIELDMODES   assert   t.fieldModes.Keys ==   u.fieldModes.Keys by { reveal oFMrFM; }//NO_FIELDMODES
    //  //  //  //      //  //  //  //      //  //  //  //      //  //  //  //

 assert k.Ready();
 assert ofv.Ready();
 assert v.Ready();
 assert rfv.Ready();
 assert m.objectInKlown(k);
 assert m.objectInKlown(ofv);
 assert m.SuperCalidFragilistic();
 assert refOK(k,ofv);
 assert m.CalidLineKV(k, v);
 assert m.CalidLineKV(ofv, rfv);
 assert HighLineKV(ofv,rfv,m);
 assert HighCalidFragilistic(m);
    assert (forall k <- m.m.Keys :: HighLineKV(k, m.m[k], m));
 assert v == m.m[k];
 assert rfv == m.m[ofv];
 assert inside(k, m.o);  //prog inside
    //  //  //  //      //  //  //  //      //  //  //  //      //  //  //  //

 var XXX := "elon";
//
//  if (ofv == m.o) {
//      assert ofv.AMFO == m.o.AMFO;
//      XXX := "pivot";
//  } else if (outside(ofv, m.o)) {
//      assert ofv != m.o;
//      assert not( ofv.AMFO >= m.o.AMFO );
//      XXX :=  "outside";
//  } else {
//      assert strictlyInside(ofv, m.o);
//      assert ofv.AMFO > m.o.AMFO;
//      assert ofv != m.o;
//      XXX :=  "inside";
//  }
//
// assert XXX != "elon";
// XXX := "elon";

  assert rfv == m.m[ofv];
//NO_FIELDMODES  assert modeOK(k, k.fieldModes[n], ofv);

 if (ofv == m.o) {
   assert ofv == m.o;
   assert ofv.AMFO == m.o.AMFO;
   assert rfv == m.m[m.o];
   assert refOK(k,ofv);
   assert strictlyInside(k, m.o);     assert strictlyInside(k, ofv);
   assert k != m.o;
   assert refBI(k,ofv);
   assert k.AMFB > {};
   assert v.AMFB >= k.AMFB;
   SetDJNZ(k.AMFB, v.AMFB);
   assert v.AMFB > {};
   assert (v.AMFB > {}) && (v.AMFB >= rfv.AMFB);
   assert refBI(v,rfv);
   assert refOK(v,rfv); //**17Sep*/   ///TRUMP
//NO_FIELDMODES     assert modeOK(v, v.fieldModes[n], rfv);
   assert HighCalidFragilistic(m);
    assert (forall k <- m.m.Keys :: HighLineKV(k, m.m[k], m));
   XXX := "pivot";
 } else if outside(ofv, m.o) {
   assert outside(ofv, m.o);   assert ofv == rfv;
   assert refOK(k,ofv);
//NO_FIELDMODES      assert modeOK(k, k.fieldModes[n], ofv);
      assert strictlyInside(k, m.o);
      assert outside(ofv, m.o);
   ItMustBI(k,ofv,m.o);
   assert refBI(k,ofv);
    assert k.AMFB > {};
    assert v.AMFB >= k.AMFB;
    SetDJNZ(k.AMFB, v.AMFB);
   assert v.AMFB > {};
   assert outside(rfv, m.m[m.o]);
   assert (v.AMFB > {}) && (v.AMFB >= rfv.AMFB);
   assert refBI(v,rfv);
   assert refOK(v,rfv); //**17Sep*/   ///TRUMP
     assert ofv  != m.o;
     assert not( ofv.AMFO >= m.o.AMFO );
//NO_FIELDMODES       assert modeOK(v, v.fieldModes[n], rfv);
     XXX :=  "outside";
   assert HighCalidFragilistic(m);
    assert (forall k <- m.m.Keys :: HighLineKV(k, m.m[k], m));
 } else if strictlyInside(ofv, m.o) {
   assert strictlyInside(ofv, m.o);
   assert refOK(k,ofv);
   assert k.Ready();
   assert v.Ready();
   assert ofv.Ready();
   assert rfv.Ready();
   assert m.objectInKlown(k);
   assert m.objectInKlown(ofv);
   assert m.SuperCalidFragilistic();
   assert m.CalidLineKV(k, v);
   assert m.CalidLineKV(ofv, rfv);
   assert HighLineKV(k, v, m);
   assert HighCalidFragilistic(m);
    assert (forall k <- m.m.Keys :: HighLineKV(k, m.m[k], m));
   assert v == m.m[k];
   assert rfv == m.m[ofv];
   assert strictlyInside(k, m.o) by { reveal AMO; assert strictlyInside(a, m.o);
                                                  assert strictlyInside(k, m.o); }
   assert strictlyInside(v, m.m[m.o]);
     RefOKisRefOK(k,ofv,v,rfv,m); //**9 Apr 2026 */
     assert refOK(v,rfv); //**17Sep*/   ///TRUMP
     assert ofv.AMFO >= m.o.AMFO;
     assert ofv != m.o;
//NO_FIELDMODES      assert modeOK(v, v.fieldModes[n], rfv);
     XXX :=  "inside";
    }    //dodgy from here - OK from 2600 via 2783
    else {
       assert not(ofv == m.o);                 AXIOMAMFOS(ofv,m.o);                     assert ofv.AMFO != m.o.AMFO;
       assert not(outside(ofv, m.o));          assert not(not(ofv.AMFO >= m.o.AMFO));   assert ofv.AMFO >= m.o.AMFO;
       assert not(strictlyInside(ofv, m.o));   assert not(ofv.AMFO > m.o.AMFO);
       assert (ofv.AMFO != m.o.AMFO) && (ofv.AMFO >= m.o.AMFO);                         assert (ofv.AMFO > m.o.AMFO);
       assert not(ofv.AMFO     > m.o.AMFO) && (ofv.AMFO > m.o.AMFO);
//NO_FIELDMODES       assert modeOK(v, v.fieldModes[n], rfv);
       assert XXX != "elon";
       assert false;
       return;
    }

  assert XXX != "elon";
//
// XXX := "elon";
//  if (ofv == m.o) {
//      assert ofv.AMFO == m.o.AMFO;
//    assert refOK(v,rfv); //**17Sep*/
//    assert modeOK(v, v.fieldModes[n], rfv);
//      XXX := "pivot";
//  } else if (outside(ofv, m.o)) {
//      assert ofv != m.o;
//      assert not( ofv.AMFO >= m.o.AMFO );
//    assert refOK(v,rfv); //**17Sep*/
//    assert modeOK(v, v.fieldModes[n], rfv);
//      XXX :=  "outside";
//  } else {
//      assert strictlyInside(ofv, m.o);
//      assert ofv.AMFO > m.o.AMFO;
//      assert ofv != m.o;
//      assert refOK(k,ofv);
//      assert (k==ofv) || refBI(k,ofv) || refDI(k,ofv);
//         if (k in ofv.owner) {
//             assert ofv != m.o;
//             assert refDI(k,ofv);
//             assert v in rfv.owner;
//             assert refDI(v,rfv);
//             assert refOK(v,rfv); //**17Sep*/
//             assert modeOK(v, v.fieldModes[n], rfv);
//             XXX :=  "insideDIREDCT";
//          } else {
//             assert refOK(k,ofv);
//             assert k !in ofv.owner;   assert not(refDI(k,ofv));
//             XXX := "PUTIN";
//             if (k==ofv) {
//                 assert v==rfv;
//                 assert refOK(v,rfv);
//                 XXX :=  "insideEQUALZ ";
//             }  else if (k != ofv) {
//                 assert k != ofv;
//                 assert k !in ofv.owner;
//                 ItMustBI(k,ofv,m.o);
//                 assert refBI(k,ofv);
//                 assert refBI(v,rfv);
//                 assert refOK(v,rfv); //**17Sep*/
//                 assert modeOK(v, v.fieldModes[n], rfv);
//                 XXX :=  "insideUSUAL";
//             }   else {
//                 // assert (k==ofv) || refBI(k,ofv) || refDI(k,ofv);
//                 assert not( k == ofv );
//                 assert not( k != ofv );
//                 assert XXX != "elon";
//                 assert false;
//                 return;
//             }
//          }
//  }

      // assert XXX != "elon";
   assert refOK(v,rfv); //**17Sep*/
  //  assert modeOK(v, v.fieldModes[n], rfv);

///PRECONDTIONs: RefOKGetsModeOK
  {
    var source := k;
    var clone  := v;
    var t := ofv;
    var u := rfv;
    assert inside(source, m.o);
//    assert strictlyInside(source, m.o);
    assert source.Ready();
    assert source.Valid();
    assert clone.Ready();
    assert t.Ready();
    assert u.Ready();
    assert m.ownersInKlown(t);
    assert m.CalidOwners();
    assert refOK(source, t);
    assert refOK(clone, u);
    assert m.objectInKlown(source);
    assert clone == m.m[ source ];
    assert n in source.fields.Keys;
    assert t == source.fields[n];
//    assert n in clone.fields.Keys;
    assert n in source.fields.Keys;
//NO_FIELDMODES     assert n in source.fieldModes.Keys;
//NO_FIELDMODES     assert n in clone.fieldModes.Keys;
    // assert u == clone.fields[n];
    // assert t in m.m.Keys;
    // assert u == m.m[ t ];
    assert clone != source;
    assert outside(t, clone);
    // assert clone.fields[n] == m.m[ t ];
    // assert clone.fields[n] == m.m[ source.fields[n] ];
    // assert m.m[ source ].fields[n] == m.m[ source.fields[n] ];
    // assert source != m.o;
    assert inside(t,source) || outside(t,source);
//    assert strictlyInside(t, source);
    assert m.ValuesOwnersReady();
    // assert forall oo <- t.owner :: strictlyInside(oo, m.o);
//NO_FIELDMODES      assert modeOK(source, source.fieldModes[n], t);
//NO_FIELDMODES     assert source.fieldModes == clone.fieldModes;
//NO_FIELDMODES     assert source.fieldModes[n] == clone.fieldModes[n];

label HERE:
    assert HighLineKV(t,u,m);
    assert HighCalidFragilistic(m);
    assert (forall k <- m.m.Keys :: HighLineKV(k, m.m[k], m));

    assert mappingOwnersThruKlownKV(t,u,m);
   } //END PRECONDS RefOKGetsModeOK


  //  RefOKGetsModeOK(k, v, n, ofv, rfv, m);

  //  assert modeOK(v, v.fieldModes[n], rfv); //**17Sep*/  ///TRUMP
   assert v.FieldValidNV(n, rfv); //*combines refOK and modeOK and n in fieldModes
   assert FVNU: v.FieldValidNV(n, rfv);
    }

//proof break
//OK from start to here…

assert rfv.Context(m.hns());

//NO_FIELDMODES    assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );

   assert m.SuperCalidFragilistic();                  assert m.from(m');
   assert HighCalidFragilistic(m);      assert HCFm: HighCalidFragilistic(m);
   assert a.Ready();    assert m.objectInKlown(a);    assert b == m.m[a];
   assert ofv.Ready();  assert m.objectInKlown(ofv);  assert rfv == m.m[ofv];
   assert afK == a.fields.Keys;    assert bfK == b.fields.Keys;
   assert a != b;
//  / /   / /   / /    / /   / /   / /    / /   / /   / /    / /   / /   / /    / /   / /   / /    / /   / /   / /    / /   / /   / /
//            b.fields := b.fields[n:= rfv];
  Xlone_Set_Field(a,b,n,ofv,rfv,m);
//  / /   / /   / /    / /   / /   / /    / /   / /   / /    / /   / /   / /    / /   / /   / /    / /   / /   / /    / /   / /   / /
   assert afK == a.fields.Keys;  assert bfK + {n} == b.fields.Keys;
//NO_FIELDMODES     assert forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes;
//NO_FIELDMODES     assert unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes );
  //  assert b.fields.Keys == old(b.fields.Keys) + {n} == bfK + {n};
  //  assert bfK + {n} == b.fields.Keys;
  //  assert n in a.fields.Keys;
  //  assert n  in afK;
                                                                          //  assert n !in bfK;
  //  assert (bfK + {n}) > bfK;
  //  assert (afK - (bfK + {n})) == ((afK - bfK) - {n});
  //  assert (afK - bfK) > ((afK - bfK) - {n});
  //  assert n in b.fields.Keys;
  //  assert (|afK - bfK|) > (|afK - (bfK + {n})|);
  //  assert (|afK - bfK|) > (|a.fields.Keys - b.fields.Keys|);
  //  assert (|afK -  (old(b.fields.Keys)+{n})|)  == (|afK - (b.fields.Keys)|);
   TieMeKangaDown(afK,bfK,n);
   assert  (ofd decreases to fielddiff(a,b));

print "RETN Clone_Field_Map: ", fmtobj(a), " pivot:", fmtobj(m.o), "\n";

   assert m.SuperCalidFragilistic();                  assert m.from(m');
   assert m.AllLinesCalid();                          assert m.CalidLineKV(ofv,rfv);
   assert mappingOwnersThruKlownKV(ofv,rfv  ,m);      assert mappingOwnersThruKlownKV(a,b,m);
             assert HighLineKV(ofv,rfv ,m);                     assert HighLineKV(a,b,m);
   forall k <- m.m.Keys ensures (HighLineKV(k, m.m[k], m)) //by
       {
          if (k == ofv) { assert HighLineKV(ofv,rfv,m); }
          else if (k == a) { assert HighLineKV(a,b,m); }
          else {
            assert old@HERE(HighCalidFragilistic(m));
            assert old@HERE(HighLineKV(k,m.m[k], m));
            assert unchanged@HERE(k);
            // assert unchanged@HERE(m.m[k]);
            assert HighLineKV(k,m.m[k], m);
          }
       }
   assert (forall k <- m.m.Keys :: HighLineKV(k, m.m[k], m));
   assert HighCalidFragilistic(m);

   assert a.Ready();    assert m.objectInKlown(a);    assert b == m.m[a];
   assert ofv.Ready();  assert m.objectInKlown(ofv);  assert rfv == m.m[ofv];

  assert  b.fields.Keys == old(b.fields.Keys) + {n};
  }
