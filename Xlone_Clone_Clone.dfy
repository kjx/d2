include "Xlone.dfy"

include "Xlone_All_Owners.dfy"
include "Xlone_All_Fields.dfy"


include "Klon-Lemmata.dfy"
// include "LUXON.dfy"


method Xlone_Clone_Clone(k : Object, m' : Klon)
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
  requires m'.ownersInKlon(k)     ///OS THIS RIOGJT OR NOT???  (july 2026)  FUCK IF I KNOW TERENCE?
  /////////////////////////////////////////////////////////////////////
   ensures klonReady(m)
   ensures klonCalid(m)
   ensures m.from(m')
   ensures m.objectInKlon(k)
   ensures m.m[k] == v
   ensures v.Context(m.hns())
   ensures klonLine(k,v,m)

//NOENSURES     ensures m.SuperCalidFragilistic()
//NOENSURES     ensures HighCalidFragilistic(m)
//NOENSURES
//NOENSURES     ensures m.from(m')
//NOENSURES     ensures m.objectInKlon(k)
//NOENSURES     ensures m.m[k] == v
//NOENSURES //NO_FIELDMODES   ensures k.fieldModes  == v.fieldModes   //hmm shouldbe some kind of map.  mapping modes?
//NOENSURES     ensures v.Ready() && v.Valid()
//NOENSURES     ensures v.Context(m.hns())
//NOENSURES     ensures m.CalidLineKV(k,v)   //JDVANCE
//NOENSURES     ensures HighLineKV(k,v,m)       //TUESDAY

{
  assert COK(k, m'.oHeap) by { reveal COKA; }
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
  print "CCC rm.owersInKlon ", fmtobj(k), " = ", rm.ownersInKlon(k), "\n";
  print "CCC k in rm.m.Keys ", fmtobj(k), " = ", (k in rm.m.Keys), "\n";


  assert klonReady(rm);
  assert klonCalid(rm);
  assert rm.ownersInKlon(k);

  if (k in rm.m.Keys) {
     print "CCC we got it\n";

    m := rm;
    v := m.m[k];
//NO_FIELDMODES           assert unchanged(m'.oHeap`fieldModes, m'.m.Values`fieldModes );


        print "RETN Clone_Clone_CLone ", fmtobj(k), " cloned while cloning owners\n";

        return;
  } // k in rm.m.Keys - i.e.   done while cloning owners



print "CCC 1001 HERE! WEESA HERE!\n";

  k.ExtraReady();

  var rowner := mapThruKlon(k.owner, rm); ///dunno when I wrote it but...
//var rowner := computeOwnerForClone(k.owner, rm); ///dunno when I wrote it but...
//var rbound := computeOwnerForClone(k.bound, rm);
assert AllReady(rowner);
//  var rbound := proposeBounds(rowner);
var rbound := mapThruKlon(k.bound, rm);
assert flatten(k.bound) >= flatten(rbound);
// ghost var XXX := insideThruKlon(k.owner, k.bound, rm);
// assert XXX;

  //Ici m'siur Napoleon!
  assume (flatten(rowner) >= flatten(rbound));  //!!!ERR
  assume (forall o <- rowner :: flatten(o.ownerBound()) >= flatten(rbound)); //!!!ERR
  assert boundsOK(rowner,rbound);

  var context := rm.hns();
 print "CCC mapped=", fmtown(rowner), " bound=", fmtown(rbound), "\n";


//
  print "Clone_Clone_CLone ", fmtobj(k), " have rowner ", fmtown(rowner) ," self not yet cloned\n";

//
print "Clone_Clone_Clone ", fmtobj(k), " boodle boodle boodle\n";

   assert boundsOK(rowner, rbound);  ///TRUMP TRUMPP TRUMPPP  //ERR

// //// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
// // /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
  v := new Object.make(k.fieldModes, rowner, context, "clone_of_" + k.nick, rbound);
print "BACK FROM MAKE with ",fmtobj(v)," owner=", fmtown(v.owner),"\n";
  assert v.Ready();   assert (v.AMFO > v.AMFX >= v.AMFB);

  assert (v.AMFB >= k.AMFB);   assert DUMBO: (v.AMFB >= k.AMFB);

// //// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
// // /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///


  assert klonReady(rm);
  assert klonCalid(rm);
  assert rm.ownersInKlon(k);
  assert k  in rm.oHeap;
  assert COK(k,rm.oHeap) by {reveal COK(); reveal COKA; }
  assert k.Ready() by {reveal COK(); reveal COKA; }
  assert (k.AMFO > k.AMFX >= k.AMFB);  assert IDIOT: (k.AMFO > k.AMFX >= k.AMFB);
  assert k !in rm.m.Keys;
  assert v !in rm.m.Values;


          assert (k.Ready() && k in rm.oHeap    && k.Valid() && k.Context(rm.oHeap));
          assert (v.Ready() && v in rm.hns({v}) && v.Valid() && v.Context(rm.hns({v})));
          assert (rm.m.Keys >= k.AMFX);
          assert (k.AMFO   >  k.AMFB) by { reveal IDIOT; }
          assert (v.AMFO   >= v.AMFB);
          assert (v.AMFB   >= k.AMFB) by { reveal DUMBO; }
      assert klonBound(k,v,rm);

      assert klonModes(k,v,rm);

          assert (m.o.Ready());
          assert (m.objectInKlon(m.o));
          assert ( (k == m.o)       <==>  (v == m.c)  );
          assert ((inside(k, m.o))   ==> (k.AMFB  <= m.o.AMFB));
          assert (outside(k, m.o)   <==>  (v == k));
          assert ( inside(k, m.o)   <==>  inside(v, m.c) );
          assert (outside(k, m.c));
          assert ((inside(k,m.o)) ==> (v !in m.oHeap));
      assert klonGeometry(k,v,rm);
      assert klonIdentity(k,v,rm);

  assert klonLine(k,v,rm);
  CKV_PRECONDS(k,v,rm);
  assert rm.CKV_preconditions(k,v);

    assert klonReady(rm);
    assert klonCalid(rm);
    assert rm.CKV_preconditions(k,v);
    assert klonLine(k,v,rm);
// //axxume rm.CKV_preconditions(k,v);
   var xm := rm.CalidKV(k,v);
//
  XCC_decreases_to_XAF(k,v,xm);
//
// //////////////////////////////////////////////////////////////////////
  assert klonReady(xm);
  assert klonCalid(xm);
  assert xm.objectInKlon(k);
  assert COK(k,xm.oHeap);
  assert v.Context(xm.hns({v}));
  assert inside(k, xm.o);
  assert xm.m[k] == v;
// //////////////////////////////////////////////////////////////////////
assert COK(k, xm.oHeap);
  m := /*FAKE_*/Xlone_All_Fields(k,v, xm); //this was deleted - who the fuck knows how long for?  . - likely can't called precondis..

assert klonLine(k,v,m);
assert klonReady(m);
assert klonCalid(m);


}//end Clone_Clone_Clone


















lemma IncorporateNewObject(rowner : Owner, rbound : Owner, k : Object, v : Object, m : Klon)
   requires klonReady(m)
   requires klonCalid(m)
   requires m.ownersInKlon(k)
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


lemma BoundsOfCloneOK(k : Object, v : Object, m : Klon)
  //suprious lemma, just use MappedBounds in Klon-Lemmata which does all the work
   requires klonReady(m)
   requires klonCalid(m)
   requires m.ownersInKlon(k)
   requires COK(k, m.oHeap)
   requires COKA: COK(k, m.oHeap)
   requires k in m.oHeap
   requires strictlyInside(k, m.o)
   requires strictlyInside(v, m.c)
   requires v.owner == mapThruKlon(k.owner, m)
   requires v.bound == mapThruKlon(k.bound, m)

   ensures boundsOK(v.owner, v.bound)
   ensures boundsOK(v.owner, v.bound)
   //ensures klonLine(k,v,m)

  {
      reveal COK();
      assert COK(k, m.oHeap) by { reveal COKA; }
    assert k.Ready();
    assert k.Valid();

assert boundsOK(k.owner, k.bound);
assert (flatten(k.owner) >= flatten(k.bound));
assert (forall o <- k.owner :: flatten(o.ownerBound()) >= flatten(k.bound));


// MappedBounds(k,v,m);

assume (flatten(v.owner) >= flatten(v.bound));
assume (forall o <- v.owner :: flatten(o.ownerBound()) >= flatten(v.bound));
assert boundsOK(v.owner, v.bound);
  }
