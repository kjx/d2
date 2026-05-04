include "Xlone.dfy"



method {:isolate_assertions} {:timeLimit 300} {:verify true} Xlone_All_Fields(a : Object, b : Object, m' : Klon)
  returns (m : Klon)

  decreases * //(m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, fielddiff(a,b), 10

  requires a.Ready() && a.Valid()

  //we're just ever called from Xlone_Via_Map  (and could be reintergrated, who knows?)
  //and  - apparently - from Xlone_Clone_Clone…
  requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound)
  requires m'.objectInKlown(a)
//prog inside
//  requires strictlyInside(a, m'.o)
  requires inside(a, m'.o)
//prog inside
  requires a in m'.m.Keys
  requires m'.m[a] == b

//START FROM XVM
  requires m'.HeapContextReady() && m'.ValuesContextReady()
  requires m'.Calid()
  requires m'.SuperCalidFragilistic()
  requires HighCalidFragilistic(m')
  requires COKA: COK(a, m'.oHeap)
  requires COK(a, m'.oHeap)

//////////////////////////////////////////////////////////////////////
  //prog WORNG  requires (klonCanKV(m',a,a))

  requires klonVMapOK(m'.m)
//  requires canVMapKV(m'.m, a, b)
  requires (a in m'.oHeap)
  requires (if (b==a) then (b in m'.oHeap) else (b !in m'.oHeap))
  requires a.Ready() && a.Valid() && a.Context(m'.oHeap)
  requires b.Ready() && b.Valid() && b.Context(m'.hns({b}))
  requires m'.ownersInKlown(a)
//NO_FIELDMODES   requires (a.fieldModes == b.fieldModes)
  requires (b.AMFX >= b.AMFB >= a.AMFB)
  requires (a.fields.Keys >= b.fields.Keys)

//////////////////////////////////////////////////////////////////////


  requires (m'.c_amfx >= flatten(m'.clbound) >= flatten(m'.o.bound))
  requires m'.oHeap >= flatten(m'.clowner) >= flatten(m'.clbound)

  requires forall oo <- a.AMFO :: oo.Ready()

  requires a.Ready() && a.Valid()
  requires m'.ownersInKlown(a)  //prog??
  requires m'.o.Ready() && m'.o.Valid()
  requires m'.objectInKlown(m'.o)
  //requires m'.CalidCanKey(a)  //prog

  requires m'.HeapContextReady()
  requires m'.ValuesContextReady()
  requires m'.Calid()
  requires HighCalidFragilistic(m') //TUESDAY

  requires a in m'.oHeap
  requires b !in m'.oHeap
  requires b in m'.hns()
  requires m'.m.Keys <= m'.oHeap
  requires allocated(m'.oHeap)
//END FROM XVM

//FIELD MODEs-ISM HACK -- shouod go into calid or at laets supercalid!
//NO_FIELDMODES   requires forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes
//NO_FIELDMODES    ensures forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes
//NO_FIELDMODES    ensures unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes )
//MODES TODO

//progTODOFUCK  ensures  m.from(m')
//KEYS  ensures  a.fields.Keys == b.fields.Keys //
   ensures m.SuperCalidFragilistic()
   ensures HighCalidFragilistic(m)
   ensures HighLineKV(a,b,m) //10Feb 2026
   ensures m.CalidLineKV(a,b)//10Feb 2026
   ensures m.from(m')
   ensures m.ownersInKlown(a)
   ensures a in m.m.Keys
//NO_FIELDMODES    ensures a.fieldModes  == b.fieldModes
   ensures m.m[a] == b
   ensures a.Ready() && a.Valid() //NOCONTEXT && a.Context(m.hns())
   ensures b.Ready() && b.Valid()
//NOCONTEXT   ensures b.Context(m.hns())
   ensures m.oHeap == m'.oHeap

  //ensures  m.m.Values >= m'.m.Values + {b} //


  modifies b`fields
{
  print "CALL Clone_All_Fields: ", fmtobj(a), " pivot:", fmtobj(m'.o), "\n";

assert m'.Calid();
  assert inside(a, m'.o);
  m := m';  assert allocated(m.oHeap);
assert m.Calid();//W8NK3R
assert HighCalidFragilistic(m); //W8NK3R II
  assert AIMO: inside(a, m.o);

assert m'.HeapContextReady() && m'.ValuesContextReady();
assert HVCR: m.HeapContextReady() && m.ValuesContextReady();

//NO_FIELDMODES assert forall z <- m.m.Keys :: z.fieldModes == m.m[z].fieldModes;
//NO_FIELDMODES assert FAM: forall z <- m.m.Keys :: z.fieldModes == m.m[z].fieldModes;

//TUESDAY15DEC2024

//prog  print "VARIANT CAF ", (m.oHeap - m.m.Keys) + {a}, " ", |a.AMFO|, " ", fielddiff(a,b), " ", 10, "\n";
  print "<<<<<<<<<<<\n";
  print "just cloned ", fmtobj(a), " as ", fmtobj(b), "\n";
  print "<<<<<<<<<<<\n";

assert m.Calid(); //W8NK3R
assert HighCalidFragilistic(m); //W8NK3R II

  print "<<<<<<<<<<<\n";
  printmapping(m.m);
  print "<<<<<<<<<<<\n";

label POSTMAPPING:

assert m.Calid();//W8NK3R
assert HighCalidFragilistic(m); assert HCFm: HighCalidFragilistic(m); //W8NK3R II
  var fieldNames : seq<string> := set2seq(a.fields.Keys);
assert HighCalidFragilistic(m) by { reveal HCFm; } //W8NK3R II  //THIS ONE!
    assert seq2set(fieldNames) <= a.fields.Keys;
    assert forall n <- fieldNames :: n in a.fields.Keys;

//NO_FIELDMODES   assert forall z <- m.m.Keys :: z.fieldModes == m.m[z].fieldModes;

 print "Clone_All_Fields fields:", fmtobj(a), " fields=", fmtseqstr(fieldNames), "\n";
  assert HighCalidFragilistic(m) by { reveal HCFm; } //W8NK3R II

  print "BLOOP BLOOP BLOOP\n";

  // for i := 0 to |fieldNames|
  //   invariant  seq2set(fieldNames) <= a.fields.Keys
  //   invariant forall n <- fieldNames :: n in a.fields.Keys
  //   invariant a.fields.Keys == old(a.fields.Keys)
  //   invariant unchanged(m'.oHeap)


assert m.HeapContextReady() && m.ValuesContextReady();

assert m.Calid();//W8NK3R
assert HighCalidFragilistic(m) by { reveal HCFm; } //W8NK3R II
assert m.objectInKlown(a);
assert m.m[a] == b;
//NO_FIELDMODES assert a.fieldModes.Keys == b.fieldModes.Keys;
//NO_FIELDMODES assert forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes;

var OLDDIFF := fielddiff(a,b);

assert allocated(m.oHeap);
label PRELOOP:
assert old@PRELOOP(allocated(m.oHeap));
assert unchanged@PRELOOP(m.oHeap);

assert a.fields.Keys >= b.fields.Keys;

while ((a.fields.Keys - b.fields.Keys) > {})

  invariant a.fields.Keys == old(a.fields.Keys)
//NO_FIELDMODES   invariant a.fieldModes.Keys == b.fieldModes.Keys
  invariant allocated(m.oHeap)
  invariant m.oHeap == m'.oHeap
  invariant unchanged(m.oHeap)
  invariant unchanged(a`fields)
  invariant m.HeapContextReady() && m.ValuesContextReady()
//NO_FIELDMODES   invariant forall z <- m.m.Keys  :: z.fieldModes == m .m[z].fieldModes
  invariant m.oHeap >= flatten(m.clowner) >= flatten(m.clbound)
  invariant m.Calid()
  invariant HighCalidFragilistic(m)
  invariant forall f <- m.m.Keys :: HighLineKV(f,m.m[f],m)
  invariant m.from(m')
  invariant m.objectInKlown(a)
  invariant m.m[a] == b
  invariant a.fields.Keys >= b.fields.Keys

  //invariant (OLDDIFF) decreases to (fielddiff(a,b))
  invariant  OLDDIFF >= fielddiff(a,b)
//NO_FIELDMODES   invariant forall z <- m'.m.Keys :: z.fieldModes == old(z.fieldModes) == m'.m[z].fieldModes
//NO_FIELDMODES   invariant forall z <- m.m.Keys :: z.fieldModes == m.m[z].fieldModes

  decreases fielddiff(a,b)

      {
  assert a.fields.Keys >= b.fields.Keys;
    OLDDIFF := fielddiff(a,b);
  assert a.fields.Keys >= b.fields.Keys;


//NO_FIELDMODES assert a.fieldModes.Keys == b.fieldModes.Keys;
assert unchanged@PRELOOP(m.oHeap);
assert unchanged@PRELOOP(a`fields);

    var n : string :| n in (a.fields.Keys - b.fields.Keys);

    print "  WHILE TLOOP field ", n, " from ", fmtobj(a), " to ", fmtobj(b), "\n";


    assert n in a.fields.Keys;
    // assert seq2set(fieldNames) <= a.fields.Keys;

    var ofv : Object := a.fields[n];

    print "  TLOOP  ",fmtobj(a),".",n," :=", fmtobj(ofv), "\n";
    print "  TLOOP m:", |m.oHeap - m.m.Keys|, " m':", |m'.oHeap - m'.m.Keys|, "\n";
    print "  TLOOP b.fieldsKeys==", b.fields.Keys, "\n";
    // print "  TINV                ", fieldNames[..i], "\n";
    // print "  TLOOPINV            ",seq2set(fieldNames[..i]),"\n";

    print "VARIANT*CAF ", |(m.oHeap - m.m.Keys) + {a}|, " ", |a.AMFO|, " ", fielddiff(a,b), " ", 10, "\n";

    var OLDFLDS := b.fields.Keys;

    var v_caf := ((m'.oHeap - m'.m.Keys +{a}), a.AMFO, (a.fields.Keys), 10);
    var v_cfm := ((m.oHeap - m.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Xlone_Field_Map

    print "v_caf ", v_caf, "\n";
    print "v_cfm ", v_cfm, "\n";

    print "okaoka ", (m'.oHeap - m'.m.Keys +{a}) >  (m.oHeap - m.m.Keys +{a}), "\n";
    print "okaoka ", (m'.oHeap - m'.m.Keys +{a}) == (m.oHeap - m.m.Keys +{a}), "\n";

print "WHOOPS-> ", |m'.oHeap - m'.m.Keys +{a}|, " ", |a.AMFO|," ",|a.fields.Keys - b.fields.Keys|," 10\n";
print "->WHOOPS ", |m'.oHeap - m'.m.Keys +{a}|, " ", |a.AMFO|," ",|a.fields.Keys - b.fields.Keys|," 5 \n";

    XAF_decreases_to_XFM(a, b, m');

//TRUMP??  assert forall o : Object :: unchanged(o);

//NO_FIELDMODES assert a.fieldModes.Keys == b.fieldModes.Keys;
//KEYS    assert a.fields.Keys == old(a.fields.Keys);
    assert unchanged@PRELOOP(m.oHeap);
  assert a.fields.Keys >= b.fields.Keys;

  //progTODOFUCKNUKE NUKE // FAKE_
  //progTODOFUCKNUKE NUKE // FAKE_
  assert n  in a.fields.Keys;
  assert n !in b.fields.Keys;

  assert a.Ready() && a.Valid();

  //we're just called from Xlone_Via_Map  (and could be reintergrated, who knows?)
//  assert m.oHeap >= flatten(m.clowner) >= flatten(m.clbound);
  assert a in m.m.Keys;
  assert m.m[a] == b;
  assert m.objectInKlown(a);
  assert inside(a, m.o) by { reveal AIMO; }

//START FROM XVMq
  assert m.HeapContextReady() && m.ValuesContextReady();
  assert m.Calid();
  assert m.from(m');
  assert COKK2A: COK(a, m.oHeap) by { reveal COKA; reveal COK(); assert COK(a, m'.oHeap); }

  assert forall f <- m.m.Keys :: HighLineKV(f,m.m[f],m);

  assert (m.c_amfx >= flatten(m.clbound) >= flatten(m.o.bound));

  assert forall oo <- a.AMFO ::oo.Ready();

  assert a.Ready() && a.Valid();

  //surely much of the following comes down from Calid()?
  assert m.o.Ready() && m.o.Valid();
  assert m.objectInKlown(m.o);
  assert m.objectInKlown(a);

//  assert m.CalidCanKey(a);

  assert m.HeapContextReady();
  assert m.ValuesContextReady();
  assert m.Calid();
  assert m.from(m');

  assert HighCalidFragilistic(m); //TUESDAY
  assert forall f <- m.m.Keys :: HighLineKV(f,m.m[f],m);  //TUESDAY


  assert a in m.oHeap;
  assert m.m.Keys <= m.oHeap;
//END FROM XVM

assert unchanged@PRELOOP(m.oHeap);
//NO_FIELDMODES   assert a.fieldModes.Keys == b.fieldModes.Keys;
//NO_FIELDMODES   assert n in b.fieldModes.Keys;
  //progTODOFUCKNUKE NUKE // FAKE_
  //progTODOFUCKNUKE NUKE // FAKE_

//NO_FIELDMODES assert a.fieldModes.Keys == b.fieldModes.Keys;
//NO_FIELDMODES assert forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// /*FAKE_*/Xlone_Field_Map(a,n,b,oldham); PRECONDITIONS
//////////////////////////////////////////////////////////////////////////////
//updated 7 Feb 2025
  assert b != a;
  assert a.Ready();
  assert a in m.m.Keys;
  assert m.m[a] == b;
  assert m.objectInKlown(a);
//prog inside
//  assert strictlyInside(a, m.o);    //   requires AMO: strictlyInside(a, m'.o)
//  assert inside(a, m.o);  //   requires AMO: strictlyInside(a, m'.o)
//assume strictlyInside(a, m.o);
//prog inside
  assert a.Valid();

  assert n  in a.fields.Keys;
  assert n !in b.fields.Keys;
//NO_FIELDMODES   assert a.fieldModes.Keys == b.fieldModes.Keys;
  assert b.Ready() && b.Valid();
  assert a.fields.Keys > b.fields.Keys;

  assert m.SuperCalidFragilistic(); //is this posible. likely NOT - if not, need to debug Xlone_Field_Map
  assert m.AllLinesCalid();
  assert HighCalidFragilistic(m); //is this posible. likely NOT

  assert COK(a, m.oHeap)  by { reveal COKK2A; reveal COK(); assert COK(a, m'.oHeap); }

  assert m.o.Ready() && m.o.Valid();
  assert m.objectInKlown(m.o);

  assert a  in m.oHeap;
  assert b !in m.oHeap;
  assert b in m.hns();
//NO_FIELDMODES   assert a.fieldModes.Keys == b.fieldModes.Keys;
//NO_FIELDMODES   assert n in b.fieldModes.Keys;

  assert m.m.Keys <= m.oHeap;
  assert allocated(m.oHeap);
//NO_FIELDMODES   assert forall z <- m.m.Keys :: z.fieldModes == m.m[z].fieldModes;

//extra shit
  assert m.oHeap >= flatten(m.clowner) >= flatten(m.clbound);
  assert m.HeapContextReady() && m.ValuesContextReady();
  assert m.Calid();
  assert m.from(m');
  assert (m.c_amfx >= flatten(m.clbound) >= flatten(m.o.bound));
  assert forall oo <- a.AMFO :: oo.Ready();

  assert m.HeapContextReady();
  assert m.ValuesContextReady();
  assert m.Calid();

  assert m.oHeap == m'.oHeap;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
  assert a.fields.Keys >= b.fields.Keys;
  assert b.fields.Keys == OLDFLDS;
  var OLDHAMFLDS := b.fields.Keys;
  var oldham := m;
  label B4:
//  / /   / /   / /    / /   / /   / /    / /   / /   / /    / /   / /   / /    / /   / /   / /    / /   / /   / /    / /   / /   / /
      m := /*FAKE_*/Xlone_Field_Map(a,n,b,oldham);
//  / /   / /   / /    / /   / /   / /    / /   / /   / /    / /   / /   / /    / /   / /   / /    / /   / /   / /    / /   / /   / /
  assert m.oHeap == oldham.oHeap;
  assert m.from(oldham);
  assert m.from(m');

  assert unchanged@PRELOOP(m.oHeap);
  assert b.fields.Keys == OLDHAMFLDS + {n};
  assert b.fields.Keys == old@B4(b.fields.Keys) + {n};

  assert b.fields.Keys == OLDFLDS + {n};
  assert a.fields.Keys >= b.fields.Keys;

//NO_FIELDMODES assert forall z <- m'.m.Keys :: z.fieldModes == old(z.fieldModes) == m'.m[z].fieldModes;
//NO_FIELDMODES assert forall z <- m.m.Keys :: z.fieldModes == m.m[z].fieldModes;

    assert seq2set(fieldNames) <= a.fields.Keys;
    assert forall n <- fieldNames :: n in a.fields.Keys;

    assert a.fields.Keys == old(a.fields.Keys);

    // assert (OLDDIFF) decreases to (fielddiff(a,b));
    // assert OLDDIFF >= fielddiff(a,b);


    assert a.fields.Keys >= b.fields.Keys;
  }//end while

  assert m.oHeap == m'.oHeap;
  assert (a.fields.Keys -  b.fields.Keys) == {};
  assert a.fields.Keys == b.fields.Keys by {
            Set2NoDifferenceEq(a.fields.Keys, b.fields.Keys); ///copilot...
            }

//NO_FIELDMODES   assert forall z <- m.m.Keys :: z.fieldModes == m.m[z].fieldModes;


    assert unchanged@PRELOOP(m.oHeap`fields);
    assert unchanged@PRELOOP(m.oHeap);
    assert unchanged@PRELOOP(a`fields);

//NO_FIELDMODES assert forall z <- m .m.Keys :: z.fieldModes == m .m[z].fieldModes;

  print "RETN Clone_All_Fields done ", fmtobj(a), "\n";

assert m.from(m');
assert m.SuperCalidFragilistic();
assert m.AllLinesCalid();
assert HighCalidFragilistic(m);
assert a.fields.Keys == b.fields.Keys;
//NO_FIELDMODES  assert a.fieldModes  == b.fieldModes;
assert m.oHeap == m'.oHeap;

CalidKVFromHighLineKV(a,b,m);
assert m.CalidLineKV(a,b);

//assert m.m.Values >= m'.m.Values + {b};
  return;
}
///end Xlone_All_Fields
