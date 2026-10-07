include "Ownership.dfy"
//include "BROWNE.dfy"




lemma K_P_Inside(oo : Object, ob : Object, co : Object, cb : Object, m : Klon)
 decreases oo.AMFO
  requires klonReady(m)
  requires klonPivot(m)
  requires klonAllLines(m)
  requires oo.Ready() && ob.Ready() && co.Ready() && cb.Ready()

  requires strictlyInside(oo,m.o)
  requires oo in m.m.Keys
  requires ob in m.m.Keys
  requires klonLine(oo,co,m)
  requires klonLine(ob,cb,m)
  requires m.m[oo] == co
  requires m.m[ob] == cb

  requires inside(oo,ob)
   ensures inside(co,cb)
{
forall o <- m.m.Keys | strictlyInside(o,m.o) ensures(m.m[o].owner == mapThruKlon(o.owner,m)) {
  assert klonLine(o,m.m[o],m);
  assert klonGeometry(o,m.m[o],m);
  assert klonIdentity(o,m.m[o],m);
  assert m.m[o].owner == mapThruKlon(o.owner,m);
  }

if (oo == ob) { assert co == cb; assert inside(co,cb); return; }

ThereIsALightThatNeverGoesOut(oo,ob);
var next :=  YouCan'tGetThereFromHereBut(oo,ob);
assert next in oo.owner;
assert inside(oo, next);
assert inside(next,ob);

if (next == ob) {
  assert ob in oo.owner;
  assert co.owner == mapThruKlon(oo.owner,m);
  assert cb in co.owner;
  assert inside(co,cb);
  return;
}
//
// var mext := m.m[next];
// assert co.owner == mapThruKlon(oo.owner,m);
// assert mext in co.owner;

assume inside(co,cb);


}


lemma MAPPING_INSIDE(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
   requires AllReady(os_sp.fAll)
   requires AllReady(cs_sp.fAll)
   requires klonCalid(m)

   requires os <= m.m.Keys
   requires forall o <- os_sp.fSin :: strictlyInside(o, m.o)
   requires cs == mapThruKlon(os,m)
   requires flownerSplitOK(os, m.o,os_sp)
   requires flownerSplitOK(cs, m.c,cs_sp)
//
//     ensures forall o <- os :: klonLine(o,m.m[o],m)
//     ensures forall o <- os :: klonGeometry(o,m.m[o],m)
//     ensures forall o <- os :: klonIdentity(o,m.m[o],m)
//     ensures forall o <- os_sp.fSin :: strictlyInside(m.m[o],m.c) && (o != m.m[o])
//  //   ensures forall o <- os_sp.fSin :: m.m[o].owner == mapThruKlon(o.owner, m)
//  //   ensures forall o <- os_sp.fSin :: m.m[o].bound == mapThruKlon(o.bound, m)
//
//     // ensures forall o <- os_sp.fSin :: woodFood(o,m.m[o],m)

  //love this beautiful symmetrical formulation
    // ensures forall o <- os_sp.fSin :: exists r <- cs_sp.fSin :: m.m[o] == r
    // ensures forall r <- cs_sp.fSin :: exists o <- os_sp.fSin :: m.m[o] == r

{
     assert cs_sp.fSin == flownerStrictlyInside(cs_sp.soup,cs_sp.pivot);
     assert os_sp.fSin == flownerStrictlyInside(os_sp.soup,os_sp.pivot);

 flownerStrictlyInside_RESULT(os_sp.soup,os_sp.pivot,os_sp.fSin);
   assert forall o <- os_sp.fAll | strictlyInside(o,os_sp.pivot) :: o in os_sp.fSin;
   assert forall o <- os_sp.fSin :: o in flatten(os_sp.soup);
   assert forall o <- os_sp.fSin :: strictlyInside(o,os_sp.pivot);
   assert forall o <- os_sp.fSin :: exists s <- os_sp.soup | o in s.AMFO :: (PART_INSIDE_OWNER(os_sp.soup,os_sp.pivot);  ownerStrictlyInside(s,os_sp.pivot,o));



 flownerStrictlyInside_RESULT(cs_sp.soup,cs_sp.pivot,cs_sp.fSin);
   assert forall o <- cs_sp.fAll | strictlyInside(o,cs_sp.pivot) :: o in cs_sp.fSin;
   assert forall o <- cs_sp.fSin :: o in flatten(cs_sp.soup);
   assert forall o <- cs_sp.fSin :: strictlyInside(o,cs_sp.pivot);
   assert forall o <- cs_sp.fSin :: exists s <- cs_sp.soup | o in s.AMFO :: (PART_INSIDE_OWNER(cs_sp.soup,cs_sp.pivot);  ownerStrictlyInside(s,cs_sp.pivot,o));



forall k <- os_sp.fSin ensures (true) {
    assert k in m.m.Keys;
    var v := m.m[k];
    assert klonLine(k,v,m);
    assert inside(k,os_sp.pivot);
    assert inside(v,cs_sp.pivot);
    }


}































type FlownerSplit = f : preFlownerSplit | f.Valid() witness * //ARGH ARGH can't make a witness with a nonnill Object field in Dafny!


datatype preFlownerSplit = preFlownerSplit(
    soup : Owner,
    pivot : Object,
    fAll : Owner,
    fSin : Owner,
    fOut : Owner,
    fPvt : Owner,
    fXpt : Owner
  ) {
    predicate Valid() {
     && (fAll == flownerAll(soup))
     && (fSin == flownerStrictlyInside(soup,pivot))
     && (fOut == flownerStrictlyOutside(soup,pivot))
     && (fPvt == flownerOnlyPivot(soup,pivot))
     && (fXpt == flownerExceptPivot(soup,pivot))
     && ((fOut + fPvt + fXpt) == flownerEverythingOutside(soup,pivot))
     && ((fOut + fPvt + fXpt) == flownerPivotlyOutside(soup,pivot))
     && (fAll == fSin + fOut + fPvt + fXpt)

     && fSin !! (fOut + fPvt + fXpt)

    }
  }




predicate flownerSplitOK(soup : OWNR, pivot : Object, split : FlownerSplit)
  requires AllReady(flatten(soup)) && pivot.Ready()
  {
      && (split.soup == soup)
      && (split.pivot == pivot)
      && (split.Valid())
  }



lemma UNPACK_flownerSplitOK(soup : OWNR, pivot : Object, split : FlownerSplit)
  requires AllReady(flatten(soup)) && pivot.Ready()
  requires flownerSplitOK(soup,pivot,split)

   ensures (split.fAll == flownerAll(soup))
   ensures (split.fAll == flatten(soup))
   ensures (split.fSin == flownerStrictlyInside(soup,pivot))
   ensures (split.fOut == flownerStrictlyOutside(soup,pivot))
   ensures (split.fPvt == flownerOnlyPivot(soup,pivot))
   ensures (split.fXpt == flownerExceptPivot(soup,pivot))
   ensures ((split.fOut + split.fPvt + split.fXpt) == flownerEverythingOutside(soup,pivot))
   ensures ((split.fOut + split.fPvt + split.fXpt) == flownerPivotlyOutside(soup,pivot))
   ensures (split.fAll == split.fSin + split.fOut + split.fPvt + split.fXpt)
   ensures split.fSin !! (split.fOut + split.fPvt + split.fXpt)
{}



































predicate outsidePivot(o : Object, pivot : Object, owner : Object) : (rv : bool)   reads {}   { inside(o, pivot) && inside(o,owner) }
  //o >= pivot is a selecwtion condition for this case
  //o >= owner should be fucken built the fuck in

lemma LEMMA_outsidePivot(o : Object, pivot : Object, owner : Object)
   requires inside(o,owner)
    ensures outsidePivot(o,pivot,owner) == inside(o,pivot)
{}

predicate onlyPivot(o : Object, pivot : Object, owner : Object) : (rv : bool)   reads {}   { inside(o, pivot) && inside(o,owner) &&  inside(pivot, owner) }
predicate exceptPivot(o : Object, pivot : Object, owner : Object) : (rv : bool) reads {}   { inside(o, pivot) && inside(o,owner) && outside(pivot, owner) }
   //should we explicitly require owner in o.AMFO  aka o inside owner?
   //well apart from the "preconditions to the preconditions" problem

function shortcutOnlyPivot(soup : OWNR, pivot : Object) : (rv : Owner)
  ensures forall p <- pivot.AMFO :: inside(pivot, p)
  ensures forall r <- rv :: inside(pivot, r)
  ensures (rv == {}) != (rv == pivot.AMFO)
  ensures (forall s <- soup :: outside(s,pivot)) ==> (rv == {})
  ensures (exists s <- soup ::  inside(s,pivot)) ==> (rv == pivot.AMFO)
  ensures forall r <- rv :: inside(pivot, r)
  ensures forall r <- rv :: exists s <- soup :: onlyPivot(s, pivot, r)
  ensures forall r <- rv :: r.Ready()
  { assume forall s <- soup :: s.Ready(); assume pivot.Ready();
    if (exists s <- soup :: inside(s,pivot)) then (pivot.AMFO) else {} }






  //  ensures ( ||  (     inside(o,pivot)       && strictlyInside(owner,pivot))  //ownerStrictlyInside
  //            ||  (  onlyPivot(o,pivot,owner) && pivotlyOutside(owner,pivot))  //owner
  //            ||  (exceptPivot(o,pivot,owner) && pivotlyOutside(owner,pivot))  //insife from outside not  pivot
  //            ||  (    outside(o,pivot)       && outside(owner,pivot)) )       //fully outside

predicate ownerStrictlyInside(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {strictlyInside(owner,pivot)}
predicate ownerInside(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {inside(owner,pivot)}
predicate ownerPivotlyOutside(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {pivotlyOutside(owner,pivot)}

predicate ownerStrictlyOutside(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {outside(owner,pivot) &&  outside(o,pivot)}
predicate ownerOutside(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {outside(owner,pivot)}
predicate ownerOnlyPivot(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {pivotlyOutside(owner,pivot) && onlyPivot(o,pivot,owner)}
predicate ownerExceptPivot(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {pivotlyOutside(owner,pivot) && exceptPivot(o,pivot,owner)}
predicate ownerOutsidePivot(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {pivotlyOutside(owner,pivot) && outsidePivot(o,owner,pivot)}




lemma PART_INSIDE_OWNER(soup : OWNR, pivot : Object)
//sort of an assertion that rememnbers parts are inside their owners
//
// when we iterate throught the "soup"  an the input list of stuff
// we'll nested-co-iterate (or is that cosubiterate? or subcoiterater??)
// therough all the owners of that part
// well this makes it easy to say that in a way that seems to get reliably
// into the middle or rhs of foralls or set comps.
  requires AllReady(flatten(soup)) && pivot.Ready()
  ensures forall o <- soup, owner <- o.AMFO :: inside(o, owner)
  ensures forall o <- soup :: o.Ready()
  ensures forall o <- soup, owner <- o.AMFO :: owner in flownerAll(soup)
{}


//  predicate root(root: Object, soup : Owner)


function flownerAll(soup : Owner) : OWNR {assume forall s <- soup :: s.Ready(); (set o <- soup, oo <- o.AMFO :: oo)}
  //yes same as nuke() etc...

function flownerStrictlyInside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerStrictlyInside(o,pivot,owner) :: owner}
function flownerStrictlyOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerStrictlyOutside(o,pivot,owner) :: owner}

function flownerInside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerInside(o,pivot,owner) :: owner}
function flownerOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerOutside(o,pivot,owner) :: owner}

function flownerOnlyPivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerOnlyPivot(o,pivot,owner) :: owner}
function flownerExceptPivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerExceptPivot(o,pivot,owner) :: owner}
function flownerOutsidePivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerOutsidePivot(o,pivot,owner) :: owner}



 function flownerEverythingOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 { flownerStrictlyOutside(soup,pivot) + flownerOutsidePivot(soup,pivot) }
 function flownerPivotlyOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
   {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerPivotlyOutside(o,pivot,owner) :: owner}

lemma FLOWNER_EVERYTHING_OUTSIDE(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()
   ensures flownerEverythingOutside(soup,pivot) == flownerPivotlyOutside(soup,pivot)
{}









lemma flownerStrictlyInside_RESULT(soup : Owner, pivot : Object, rv : Owner)
 //verfies!!!
  requires AllReady(flatten(soup)) && pivot.Ready() && AllReady(flatten(rv))
  requires flownerStrictlyInside(soup,pivot) == rv
   ensures forall r <- flatten(soup) | strictlyInside(r,pivot) :: r in rv
   ensures forall r <- rv :: r in flatten(soup)
   ensures forall r <- rv :: strictlyInside(r,pivot)
   ensures forall owner <- rv :: exists o <- soup | owner in o.AMFO ::
          (PART_INSIDE_OWNER(soup,pivot);  ownerStrictlyInside(o,pivot,owner))
{}
