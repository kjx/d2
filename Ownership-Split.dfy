include "Ownership.dfy"
include "Bound.dfy"

include "Ownership-Flatten.dfy" //be nice to remove this...

//apparently this file has no Klon,  should be renamed.
//Ownership Flowner?

// the stuff that does NOT depend on the Klon are doing the "horizontal" mapping
// between owner (bigger/deeper)  and  bound (smaller/shallower)
//
// actually, most of the code in this file is just about
// categorising owners of just one "soup"
// so the basis of that comparison, but not acutally doing it

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
    predicate {:timeLimit 60} Valid() {
      assume AllReady(flatten(soup));
      assume pivot.Ready();
    //  && AllReady(flatten(soup))   //should do better than that…
    //  && pivot.Ready() //…ditto
     && (fAll == flownerAll(soup) == flatten(soup))
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
 // requires AllReady(soup) && pivot.Ready()
  {
      && (split.soup == soup)
      && (split.pivot == pivot)
      && (split.Valid())
  }


lemma UNPACK_flownerSplitOK(soup : OWNR, pivot : Object, split : FlownerSplit)
  requires AllReady(flatten(soup)) && pivot.Ready()

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

   ensures forall o <- (split.fOut) :: outside(o,pivot)
   ensures forall o <- (split.fXpt) :: outside(o,pivot)
   ensures forall o <- (split.fOut+split.fXpt) :: outside(o,pivot)
{}

// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
























///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////
//// Tertiary Pivot predicates
////
////

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

predicate ownerDisjunctPivot(o : Object, pivot : Object, owner : Object) : (rv : bool)
    requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
        {ownerStrictlyOutside(o,pivot,owner) || ownerExceptPivot(o,pivot,owner)}
predicate ownerWithoutPivot(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {outside(pivot,owner)}








///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////
//// "Flowner" functions - functions that flatten a "soup" into a set  divided in some why with a pivot
////
////

function flownerAll(soup : Owner) : OWNR {assume forall s <- soup :: s.Ready(); (set o <- soup, oo <- o.AMFO :: oo)}
  //yes same as flatten() etc...

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

function flownerDisjunctPivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerDisjunctPivot(o,pivot,owner) :: owner}


 function flownerEverythingOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 { flownerStrictlyOutside(soup,pivot) + flownerOutsidePivot(soup,pivot) }
 function flownerPivotlyOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
   {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerPivotlyOutside(o,pivot,owner) :: owner}








///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////
//// Non - "Flowner" flattening functions - functions that flatten a "soup" into a set  divided in some why with a pivot
//// alternatives, often recursive
////

function collectStrictlyInside(soup : Owner, pivot : Object) : (rv : set<Object>)
///version from BROWNE
  decreases allAMFOs(soup), 2
   requires forall o <- soup :: o.Ready()
    ensures forall r <- rv :: strictlyInside(r,pivot)
    ensures forall r <- rv :: r in flatten(soup)
    { (set o <- soup, ooo <- collectStrictlyInsideObject(o,pivot) :: ooo) }


function collectStrictlyInsideObject(o : Object, pivot : Object) : (rv : set<Object>)
///version from BROWNE
  decreases o.AMFO, 1
   requires o.Ready()
    ensures forall r <- rv :: strictlyInside(r,pivot)
    ensures forall r <- rv :: r in o.AMFO
    { if (not(strictlyInside(o,pivot))) then ({}) else ({o}+collectStrictlyInside(o.owner,pivot)) }



function arghStrictlyInside(o : Object, pivot : Object) : Owner
  decreases o.AMFO
   requires o.Ready()
 { allStrictlyInside(argh(o), pivot) }


//
// function collectStrictlyInsideObject(o : Object, pivot : Object) : (rv : set<Object>)
//   decreases o.AMFO, 10
// //   requires o.Ready()
//    ensures rv <= o.AMFO
//     { assume o.Ready(); if (not(strictlyInside(o,pivot))) then ({}) else ({o}+collectStrictlyInside(o.owner,pivot)) }
//
//
// function collectStrictlyInside(soup : Owner, pivot : Object) : (rv : set<Object>)
//   // requires forall o <- soup :: o.Ready()
//       decreases allAMFOs(soup), 20
//         ensures rv <= flatten(soup)
//     { assume forall o <- soup :: o.Ready(); (set o <- soup, ooo <- collectStrictlyInsideObject(o,pivot) :: ooo) }
//




///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////
//// RESULT lemmas that expand on the results of the flowner functions
////
////


lemma {:timeLimit 30} collectStrictlyInside_RESULT(soup : Owner, pivot : Object, rv : Owner)
 decreases allAMFOs(soup)
  requires AllReady(flatten(soup)) && pivot.Ready() && AllReady(flatten(rv))
  requires collectStrictlyInside(soup,pivot) == rv
   //ensures forall r <- flatten(soup) | strictlyInside(r,pivot) :: r in rv //err
   ensures forall r <- rv :: r in flatten(soup)
  ensures forall r <- rv :: strictlyInside(r,pivot)  //err
  //  ensures forall owner <- rv :: exists o <- soup | owner in o.AMFO ::
  //         (PART_INSIDE_OWNER(soup,pivot);  ownerStrictlyInside(o,pivot,owner))
{
  if (soup == {}) {return;}

  forall oo <- soup ensures (true) {
    var rs := collectStrictlyInsideObject(oo, pivot);
    assert (oo in rs) ==> strictlyInside(oo,pivot);
    collectStrictlyInside_RESULT(oo.owner,pivot, collectStrictlyInside(oo.owner,pivot) );
   assert rs == if (strictlyInside(oo,pivot)) then {oo} + collectStrictlyInside(oo.owner, pivot) else {};
   assert forall r <- rs :: strictlyInside(r,pivot);
    assert rs <= flatten(soup);
  }
}


lemma flownerOnlyPivot_RESULT(soup : Owner, pivot : Object, rv : Owner)
//verified 23Sep2026 - compare ONLY_PIVOT
  requires AllReady(flatten(soup)) && pivot.Ready() && AllReady(flatten(rv))
  requires flownerOnlyPivot(soup,pivot) == rv
   ensures (pivot  in flownerAll(soup))  ==> (rv == pivot.AMFO)
   ensures (pivot !in flownerAll(soup)) ==> (rv == {})
   {
   assert rv == flownerOnlyPivot(soup, pivot);
FLOWNER_SHORTCUT_OnlyPivot(soup, pivot, rv);
   assert rv == shortcutOnlyPivot(soup, pivot);
 LEMMA_shortcutOnlyPivot1(soup, pivot, rv);
   }



lemma flownerStrictlyOutside_RESULT(soup : Owner, pivot : Object, rv : Owner)
 //verfies!!!
  requires AllReady(flatten(soup)) && pivot.Ready() && AllReady(flatten(rv))
  requires flownerStrictlyOutside(soup,pivot) == rv
   ensures forall owner <- rv :: exists o <- soup | owner in o.AMFO ::
          (PART_INSIDE_OWNER(soup,pivot);  ownerStrictlyOutside(o,pivot,owner))
{}



lemma flownerStrictlyInside_RESULT(soup : Owner, pivot : Object, rv : Owner)
 //verfies!!!  -- coould tweak to take a split I guess
  requires AllReady(flatten(soup)) && pivot.Ready() && AllReady(flatten(rv))
  requires flownerStrictlyInside(soup,pivot) == rv
   ensures forall r <- flatten(soup) | strictlyInside(r,pivot) :: r in rv
   ensures forall r <- rv :: r in flatten(soup)
   ensures forall r <- rv :: strictlyInside(r,pivot)
   ensures forall owner <- rv :: exists o <- soup | owner in o.AMFO ::
          (PART_INSIDE_OWNER(soup,pivot);  ownerStrictlyInside(o,pivot,owner))
{}





///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////
//// MONOTONIC lemmas about on the results of the flowner functions
////
////





lemma flownerAll_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
 //given the input is stupidlyHappy (close to flatten(soup0) >= close to(soup1)
 //then all the "partials" are at MONOTNOIC
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()

//  requires stupidlyHappy(soup0, soup1, pivot)

  requires flownerAll(soup0) >= flownerAll(soup1)
  requires flatten(soup0) >= flatten(soup1)

//requires flownerAll(soup0) >= flownerAll(sup1)
//  requires flatten(soup0) >= flatten(soup1)

   ensures flownerStrictlyInside(soup0,pivot)    >= flownerStrictlyInside(soup1,pivot)
   ensures flownerStrictlyOutside(soup0,pivot)   >= flownerStrictlyOutside(soup1,pivot)
   ensures flownerOnlyPivot(soup0,pivot)         >= flownerOnlyPivot(soup1,pivot)
   ensures flownerExceptPivot(soup0,pivot)       >= flownerExceptPivot(soup1,pivot)
   ensures flownerOutsidePivot(soup0,pivot)      >= flownerOutsidePivot(soup1,pivot)
   ensures flownerEverythingOutside(soup0,pivot) >= flownerEverythingOutside(soup1,pivot)
   ensures flownerPivotlyOutside(soup0,pivot)    >= flownerPivotlyOutside(soup1,pivot)

   ensures flownerDisjunctPivot(soup0,pivot)     >= flownerDisjunctPivot(soup1,pivot)
{
    flownerStrictlyInside_MONOTONIC(soup0, soup1, pivot);
    flownerStrictlyOutside_MONOTONIC(soup0, soup1, pivot);
    flownerOnlyPivot_MONOTONIC(soup0, soup1, pivot);
    flownerExceptPivot_MONOTONIC(soup0, soup1, pivot);
    flownerOutsidePivot_MONOTONIC(soup0, soup1, pivot);
    flownerPivotlyOutside_MONOTONIC(soup0, soup1, pivot);

}





lemma flownerAll_SONOMONIC(xo : Owner, xo_sp : FlownerSplit, xb : Owner, xb_sp : FlownerSplit, pivot : Object)
  requires AllReady(flatten(xo))
  requires AllReady(flatten(xb))
  requires pivot.Ready()
  requires flownerSplitOK(xo,pivot,xo_sp)
  requires flownerSplitOK(xb,pivot,xb_sp)
  requires true  //wjztaever upi wanmt tp wrote  <== obviously too tired to continue

  requires (xb_sp.fSin >= xb_sp.fSin)
  requires (xb_sp.fOut >= xb_sp.fOut)
  requires (xb_sp.fPvt >= xb_sp.fPvt)
  requires (xb_sp.fXpt >= xb_sp.fXpt)

   ensures (xb_sp.fAll >= xb_sp.fAll)
//   ensures stupidlyHappy(xo, xb, pivot)
{
  UNPACK_flownerSplitOK(xo,pivot,xo_sp);
  UNPACK_flownerSplitOK(xb,pivot,xb_sp);
}


lemma flownerAll_SONOMONIC_AND_HAPPY_AND_BOUNDS(xo : Owner, xo_sp : FlownerSplit, xb : Owner, xb_sp : FlownerSplit, pivot : Object)
  requires AllReady(flatten(xo))
  requires AllReady(flatten(xb))
  requires pivot.Ready()
  requires (forall r <- xb | outside(r,pivot) :: exists s <- xo :: outside(s,pivot) && inside(s,r))
  requires (forall o <- xo :: flatten(o.ownerBound()) >= flatten(xb))

  requires flownerSplitOK(xo,pivot,xo_sp)
  requires flownerSplitOK(xb,pivot,xb_sp)
  requires true  //wjztaever upi wanmt tp wrote  <== obviously too tired to continue

  requires (xo_sp.fSin >= xb_sp.fSin)
  requires (xo_sp.fOut >= xb_sp.fOut)
  requires (xo_sp.fPvt >= xb_sp.fPvt)
  requires (xo_sp.fXpt >= xb_sp.fXpt)

   ensures (xo_sp.fAll >= xb_sp.fAll)
   ensures stupidlyHappy(xo, xb, pivot)
{
  UNPACK_flownerSplitOK(xo,pivot,xo_sp);
  UNPACK_flownerSplitOK(xb,pivot,xb_sp);
  assert (forall r <- xb | outside(r,pivot) :: exists s <- xo :: outside(s,pivot) && inside(s,r));
  assert (xo_sp.fAll >= xb_sp.fAll);
  assert (flatten(xo) >= flatten(xb));

  assert stupidlyHappy(xo, xb, pivot);
  assert boundsOK(xo, xb);

}



lemma FLOWNER_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
//   ensures flownerStrictlyInside(soup0,pivot)    >= flownerStrictlyInside(soup1,pivot)
  //  ensures flownerStrictlyOutside(soup0,pivot)      >= flownerStrictlyOutside(soup1,pivot)
//   ensures flownerOnlyPivot(soup0,pivot)         >= flownerOnlyPivot(soup1,pivot)
//   ensures flownerExceptPivot(soup0,pivot)       >= flownerExceptPivot(soup1,pivot)
//   ensures flownerOutsidePivot(soup0,pivot)       >= flownerOutsidePivot(soup1,pivot)
//   ensures flownerEverythingOutside(soup0,pivot) >= flownerEverythingOutside(soup1,pivot)
   ensures flownerPivotlyOutside(soup0,pivot)    >= flownerPivotlyOutside(soup1,pivot)
{
 assert flownerPivotlyOutside(soup0,pivot)
   == (set o <- soup0, owner <- o.AMFO | PART_INSIDE_OWNER(soup0,pivot); ownerPivotlyOutside(o,pivot,owner) :: owner);
 assert flownerPivotlyOutside(soup0,pivot)
   == (set o <- soup0, owner <- o.AMFO | PART_INSIDE_OWNER(soup0,pivot); pivotlyOutside(owner,pivot) :: owner);
 assert flownerPivotlyOutside(soup0,pivot)
   == (set owner <- flownerAll(soup0) | PART_INSIDE_OWNER(soup0,pivot); pivotlyOutside(owner,pivot) :: owner);
 assert flownerPivotlyOutside(soup1,pivot)
   == (set o <- soup1, owner <- o.AMFO | PART_INSIDE_OWNER(soup1,pivot); ownerPivotlyOutside(o,pivot,owner) :: owner);
 assert flownerPivotlyOutside(soup1,pivot)
   == (set o <- soup1, owner <- o.AMFO | PART_INSIDE_OWNER(soup1,pivot); pivotlyOutside(owner,pivot) :: owner);
 assert flownerPivotlyOutside(soup1,pivot)
   == (set owner <- flownerAll(soup1) | PART_INSIDE_OWNER(soup1,pivot); pivotlyOutside(owner,pivot) :: owner);
 assert flownerAll(soup0) >= flownerAll(soup1);
 assert (set owner <- flownerAll(soup0) | PART_INSIDE_OWNER(soup0,pivot); pivotlyOutside(owner,pivot) :: owner)
     >= (set owner <- flownerAll(soup1) | PART_INSIDE_OWNER(soup1,pivot); pivotlyOutside(owner,pivot) :: owner);
 assert flownerPivotlyOutside(soup0,pivot)    >= flownerPivotlyOutside(soup1,pivot);
}

lemma flownerPivotlyOutside_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
 //why is this here.  didn't have a body :-(
 //verifié 24Sept2026
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
//   ensures flownerStrictlyInside(soup0,pivot)    >= flownerStrictlyInside(soup1,pivot)
//   ensures flownerStrictlyOutside(soup0,pivot)      >= flownerStrictlyOutside(soup1,pivot)
//   ensures flownerOnlyPivot(soup0,pivot)         >= flownerOnlyPivot(soup1,pivot)
//   ensures flownerExceptPivot(soup0,pivot)       >= flownerExceptPivot(soup1,pivot)
//   ensures flownerOutsidePivot(soup0,pivot)       >= flownerOutsidePivot(soup1,pivot)
//   ensures flownerEverythingOutside(soup0,pivot) >= flownerEverythingOutside(soup1,pivot)
   ensures flownerPivotlyOutside(soup0,pivot)    >= flownerPivotlyOutside(soup1,pivot)
{
FLOWNER_MONOTONIC(soup0,soup1,pivot);
}

lemma flownerStrictlyInside_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
 //why is this here.  didn't have a body :-(
 //verifié 24Sept2026
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
   ensures flownerStrictlyInside(soup0,pivot)    >= flownerStrictlyInside(soup1,pivot)
   {
    FLOWNER_MONOTONIC(soup0,soup1,pivot);
    assert flownerPivotlyOutside(soup0,pivot)    >= flownerPivotlyOutside(soup1,pivot);

    FLOWNER_ALL_ALL(soup0, pivot);
    assert flownerStrictlyInside(soup0,pivot) == flownerAll(soup0) - flownerPivotlyOutside(soup0,pivot);
    FLOWNER_ALL_ALL(soup1, pivot);
    assert flownerStrictlyInside(soup1,pivot) == flownerAll(soup1) - flownerPivotlyOutside(soup1,pivot);

    assert flownerStrictlyInside(soup0,pivot)    >= flownerStrictlyInside(soup1,pivot);
   }


lemma {:timeLimit 120}  flownerExceptPivot_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
////verified 25Sep2026
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flatten(soup0) >= flatten(soup1)
//requires flownerAll(soup0) >= flownerAll(soup1)
   ensures flownerExceptPivot(soup0,pivot)  >= flownerExceptPivot(soup1,pivot)
{
  var rv0 := flownerExceptPivot(soup0,pivot);
  var rv1 := flownerExceptPivot(soup1,pivot);
  assert  flownerAll(soup0) >= flownerAll(soup1);
  assert rv0 == (set o <- soup0, owner <- o.AMFO | PART_INSIDE_OWNER(soup0,pivot); ownerExceptPivot(o,pivot,owner) :: owner);
  assert rv1 == (set o <- soup1, owner <- o.AMFO | PART_INSIDE_OWNER(soup1,pivot); ownerExceptPivot(o,pivot,owner) :: owner);
  assert rv0 >= rv1;
  assert flownerExceptPivot(soup0,pivot)     >= flownerExceptPivot(soup1,pivot);
}



lemma flownerOnlyPivot_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
////verified 23Sep2026
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
   ensures flownerOnlyPivot(soup0,pivot)  >= flownerOnlyPivot(soup1,pivot)
{
  var rv0 := flownerOnlyPivot(soup0,pivot);
  flownerOnlyPivot_RESULT(soup0,pivot,rv0);
  var rv1 := flownerOnlyPivot(soup1,pivot);
  flownerOnlyPivot_RESULT(soup1,pivot,rv1);
  assert flownerOnlyPivot(soup0,pivot)     >= flownerOnlyPivot(soup1,pivot);
}


lemma flownerOutsidePivot_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
//feelin' proovie!
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
   ensures flownerOutsidePivot(soup0,pivot)  >= flownerOutsidePivot(soup1,pivot)
{
  var rv0 := flownerOutsidePivot(soup0,pivot);
  var rv1 := flownerOutsidePivot(soup1,pivot);
  var op0 := flownerOnlyPivot(soup0,pivot);
  var op1 := flownerOnlyPivot(soup1,pivot);
  var ep0 := flownerExceptPivot(soup0,pivot);
  var ep1 := flownerExceptPivot(soup1,pivot);

  flownerOnlyPivot_MONOTONIC(soup0,soup1,pivot);
  flownerExceptPivot_MONOTONIC(soup0,soup1,pivot);
  FLOWNER_CONJOINT(soup0,pivot,rv0,op0,ep0);
  FLOWNER_CONJOINT(soup1,pivot,rv1,op1,ep1);
  assert rv0 >= rv1;
  assert flownerOutsidePivot(soup0,pivot)     >= flownerOutsidePivot(soup1,pivot);
}




lemma {:timeLimit 120} flownerStrictlyOutside_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
  requires flatten(soup0) >= flatten(soup1)

  requires stupidlyHappy(soup0, soup1, pivot)


//X   ensures flownerStrictlyOutside(soup0,pivot)  >= flownerStrictlyOutside(soup1,pivot)
{
   var rv0 := flownerStrictlyOutside(soup0,pivot);
   flownerStrictlyOutside_RESULT(soup0,pivot,rv0);
   assert forall owner <- rv0 :: exists o <- soup0 | owner in o.AMFO ::
          (PART_INSIDE_OWNER(soup0,pivot);
           && outside(o,pivot)
           && ownerStrictlyOutside(o,pivot,owner));

   var rv1 := flownerStrictlyOutside(soup1,pivot);
   flownerStrictlyOutside_RESULT(soup1,pivot,rv1);
   assert forall owner <- rv1 :: exists s <- soup1 | owner in s.AMFO ::
          (PART_INSIDE_OWNER(soup1,pivot);  ownerStrictlyOutside(s,pivot,owner));

   forall owner <- rv1 ensures (exists o <- soup0 | owner in o.AMFO ::
       (PART_INSIDE_OWNER(soup0,pivot);
          assert o.Ready();
          assert pivot.Ready();
          assert owner.Ready();
          assert inside(o, owner);
         ownerStrictlyOutside(o,pivot,owner)))  //by
     {
        assert exists s <- soup1 | owner in s.AMFO ::
          (PART_INSIDE_OWNER(soup1,pivot);
          && outside(s,pivot)
          && ownerStrictlyOutside(s,pivot,owner));
        var s :| (s in soup1) && (owner in s.AMFO) && outside(s,pivot) && (PART_INSIDE_OWNER(soup1,pivot);  ownerStrictlyOutside(s,pivot,owner));
        assert flatten(soup0) >= flatten(soup1);
        assert exists o <- soup0 :: s in o.AMFO &&
          (PART_INSIDE_OWNER(soup0,pivot);  ownerStrictlyOutside(o,pivot,owner));
        var o :| (o in soup0) && (s in o.AMFO) &&
          (PART_INSIDE_OWNER(soup0,pivot);  ownerStrictlyOutside(o,pivot,owner));
        assert ownerStrictlyOutside(o,pivot,owner);
        assert outside(o,pivot);


  assert AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready();
  assert flatten(soup0) >= flatten(soup1);
  assert s in soup1;
  assert outside(s,pivot);
  assert owner in s.AMFO;
  assert owner in flatten(soup1);
  assert outside(owner,pivot);
  assert s in o.AMFO;
  assert o in soup0;
  assert outside(o,pivot);
  assert forall q <- flatten(soup0) :: q.Ready();
  assert ownerStrictlyOutside(s,pivot,owner);

           EXISTENTIAL_FUCKED(soup0, soup1, s, pivot, owner, o);
     }
}






///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////
//// "shortcut" defintions & lemmas
////  basically recursive alternatives?
////











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


lemma LEMMA_shortcutOnlyPivot0(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == shortcutOnlyPivot(soup, pivot))

   ensures forall r <- rv :: inside(pivot, r)
   ensures forall r <- rv :: exists s <- soup :: inside(s,r)
   ensures forall r <- rv :: inside(pivot, r) && (exists s <- soup :: inside(s,r))
   ensures forall r <- rv :: exists s <- soup :: onlyPivot(s,pivot,r)
{}

lemma LEMMA_shortcutOnlyPivot1(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == shortcutOnlyPivot(soup, pivot))
   ensures (forall s <- soup :: outside(s,pivot)) ==> (rv == {})
   ensures (exists s <- soup ::  inside(s,pivot)) ==> (rv >  {})
   ensures (exists s <- soup ::  inside(s,pivot)) ==> (rv == pivot.AMFO)
{}









lemma ONLY_PIVOT(soup : OWNR, pivot : Object, rv : Owner)
   requires AllReady(flatten(soup)) && pivot.Ready()

  requires || (flownerOnlyPivot(soup,pivot) == rv)
           || (flattenOnlyPivot(soup,pivot) == rv)
           || (shortcutOnlyPivot(soup,pivot) == rv)

   ensures ((pivot  in flownerAll(soup)) || (pivot  in flatten(soup)))
       ==> (rv == pivot.AMFO)
   ensures ((pivot !in flownerAll(soup)) && (pivot !in flatten(soup)))
       ==> (rv == {})

    ensures shortcutOnlyPivot(soup, pivot) == flattenOnlyPivot(soup, pivot) == flownerOnlyPivot(soup,pivot) == rv
 {
   assume AllReady(flatten(soup));
   assume pivot.Ready();
   LEMMA_shortcutVSflatten2(soup, pivot, shortcutOnlyPivot(soup, pivot), flattenOnlyPivot(soup, pivot));
}



lemma FLOWNER_SHORTCUT_OnlyPivot(soup : OWNR, pivot : Object, rv : Owner)
 //verified 21 Sep 2026
  requires AllReady(flatten(soup)) && pivot.Ready()
   ensures shortcutOnlyPivot(soup, pivot) == flattenOnlyPivot(soup, pivot)
   ensures (shortcutOnlyPivot(soup, pivot) == flattenOnlyPivot(soup, pivot) == {}) || (shortcutOnlyPivot(soup, pivot) == flattenOnlyPivot(soup, pivot) == pivot.AMFO)

   ensures shortcutOnlyPivot(soup, pivot) == flownerOnlyPivot(soup, pivot)
   ensures (shortcutOnlyPivot(soup, pivot) == flownerOnlyPivot(soup, pivot) == {}) || (shortcutOnlyPivot(soup, pivot) == flownerOnlyPivot(soup, pivot) == pivot.AMFO)
{
  LEMMA_shortcutVSflatten2(soup, pivot, shortcutOnlyPivot(soup, pivot), flattenOnlyPivot(soup, pivot));
}



lemma  STUPIDLY_HAPPY_To_OnlyPivot(xo : Owner, xb : Owner,
      xo_sp : FlownerSplit, xb_sp : FlownerSplit, pivot : Object)
 //verified 21Sep2026
  requires AllReady(flatten(xo)) && AllReady(flatten(xb))
  requires xo_sp.fAll >= xb_sp.fAll // or should this be stupid happy or something???
//  requires stupidlyHappy(xo,xb,pivot)      //ISNT THIS PRETTY MUCH CIRCULAR:??
  requires pivot.Ready()
  requires flownerSplitOK(xo, pivot, xo_sp)
  requires flownerSplitOK(xb, pivot, xb_sp)

   ensures xo_sp.fAll == flownerAll(xo)
   ensures xb_sp.fAll == flownerAll(xb)
   ensures xo_sp.fPvt == flownerOnlyPivot(xo, pivot)
   ensures xb_sp.fPvt == flownerOnlyPivot(xb, pivot)

   ensures (pivot  in xo_sp.fAll) ==> (xo_sp.fPvt == pivot.AMFO)
   ensures (pivot !in xo_sp.fAll) ==> (xo_sp.fPvt == {})
   ensures (pivot  in xb_sp.fAll) ==> (xb_sp.fPvt == pivot.AMFO)
   ensures (pivot !in xb_sp.fAll) ==> (xb_sp.fPvt == {})
   ensures (pivot  in xb_sp.fAll) ==> (pivot  in xo_sp.fAll)
{
   UNPACK_flownerSplitOK(xo,pivot,xo_sp);
   UNPACK_flownerSplitOK(xb,pivot,xb_sp);

      ONLY_PIVOT(xo,pivot,xo_sp.fPvt);
      ONLY_PIVOT(xb,pivot,xb_sp.fPvt);
}


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////
//// other lemmas about on the results of the flowner functions
////
////



lemma FLOWNER_ALL_ALL(soup : OWNR, pivot : Object)
//can be replaced with split.Valid()
 //verified 20 Sep 2026
  requires AllReady(flatten(soup)) && pivot.Ready()

   ensures flownerAll(soup) == flownerStrictlyInside(soup,pivot) + flownerStrictlyOutside(soup,pivot) + flownerOutsidePivot(soup,pivot)
   ensures flownerOutsidePivot(soup,pivot) == (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))

   ensures flownerAll(soup) == flownerStrictlyInside(soup,pivot) +  flownerStrictlyOutside(soup,pivot) + (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))
   ensures flownerAll(soup) == flownerStrictlyInside(soup,pivot) +  flownerPivotlyOutside(soup,pivot)

   ensures                     flownerStrictlyInside(soup,pivot) !! (flownerStrictlyOutside(soup,pivot) + flownerOutsidePivot(soup,pivot))
   ensures                     flownerStrictlyInside(soup,pivot) !! flownerPivotlyOutside(soup,pivot)

   ensures flownerEverythingOutside(soup,pivot) == flownerStrictlyOutside(soup,pivot) + flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot)
   ensures flownerPivotlyOutside(soup,pivot) == flownerStrictlyOutside(soup,pivot) + flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot)
{}



function flownerSplit(os : Owner,pivot : Object) : (rv : FlownerSplit)
  requires AllReady(flatten(os)) && pivot.Ready()
   ensures flownerSplitOK(os, pivot, rv)
 {
  var fAll := flownerAll(os);
  var fSin := flownerStrictlyInside(os,pivot);
  var fOut := flownerStrictlyOutside(os,pivot);
  var fPvt := flownerOnlyPivot(os,pivot);
  var fXpt := flownerExceptPivot(os,pivot);
  FLOWNER_ALL_ALL(os,pivot);
  var fs := preFlownerSplit(os,pivot,fAll,fSin,fOut,fPvt,fXpt);
  assert fs.Valid();
  fs
 }




lemma WITHOUT_PIVOT_0(o : Object, pivot : Object, owner : Object)
  requires o.Ready() && pivot.Ready() && owner.Ready()
  requires inside(o, owner)
   ensures ownerDisjunctPivot(o,pivot,owner) <==> (ownerStrictlyOutside(o,pivot,owner)        || ownerExceptPivot(o,pivot,owner))
   ensures ownerDisjunctPivot(o,pivot,owner) <==> (ownerStrictlyOutside(o,pivot,owner)        || (pivotlyOutside(owner,pivot) && exceptPivot(o,pivot,owner)))
   ensures ownerDisjunctPivot(o,pivot,owner) <==> ((outside(owner,pivot) && outside(o,pivot)) || ownerExceptPivot(o,pivot,owner))
   ensures ownerDisjunctPivot(o,pivot,owner) <==> ((outside(owner,pivot) && outside(o,pivot)) || (pivotlyOutside(owner,pivot) && exceptPivot(o,pivot,owner)))

   ensures ownerStrictlyOutside(o,pivot,owner) <==> (outside(owner,pivot) && outside(o,pivot))

   ensures ownerExceptPivot(o,pivot,owner)     <==> (pivotlyOutside(owner,pivot)                  && exceptPivot(o,pivot,owner))
   ensures ownerExceptPivot(o,pivot,owner)     <==> (((outside(owner,pivot) || (owner == pivot))) && exceptPivot(o,pivot,owner))

   ensures exceptPivot(o,pivot,owner) <==>  (inside(o, pivot) && inside(o,owner) && outside(pivot, owner))
   ensures exceptPivot(o,pivot,owner) <==>  (inside(o, pivot) &&                    outside(pivot, owner))

   ensures ownerExceptPivot(o,pivot,owner)     <==> (((outside(owner,pivot) || (owner == pivot))) &&  (inside(o, pivot) && outside(pivot, owner)))

   ensures ownerDisjunctPivot(o,pivot,owner) <==>
          ( ||  (outside(owner,pivot)                      && outside(o,pivot))
            || ((outside(owner,pivot) || (owner == pivot)) && (inside(o,pivot) && outside(pivot,owner))) )
     {}


lemma WITHOUT_PIVOT_1(soup : OWNR, pivot : Object)
    requires AllReady(flatten(soup)) && pivot.Ready()
     ensures flownerDisjunctPivot(soup,pivot) == flownerStrictlyOutside(soup,pivot) + flownerExceptPivot(soup,pivot)
{}







lemma FLOWNER_EVERYTHING_OUTSIDE(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()
   ensures flownerEverythingOutside(soup,pivot) == flownerPivotlyOutside(soup,pivot)
{}
//could merge these two, but thiss lets us be more specific when calling them,
lemma FLOWNER_EVERYTHING_EVERYTHING(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()
   ensures flownerEverythingOutside(soup,pivot) == flownerStrictlyOutside(soup,pivot) + flownerOutsidePivot(soup,pivot)
   ensures flownerEverythingOutside(soup,pivot) == flownerStrictlyOutside(soup,pivot) + (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))
{}

lemma FLOWNER_EVERYTHING_EVERYWHERE(soup : OWNR, pivot : Object, FEO : Owner, FFO : Owner, FOP : Owner, FEP : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
  requires FEO == flownerEverythingOutside(soup,pivot)
  requires FFO == flownerStrictlyOutside(soup,pivot)
  requires FOP == flownerOnlyPivot(soup,pivot)
  requires FEP == flownerExceptPivot(soup,pivot)
   ensures FEO == FFO + FOP + FEP
   ensures flownerEverythingOutside(soup,pivot) == flownerStrictlyOutside(soup,pivot) + (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))
{}

lemma FLOWNER_ALL_EVERYTHING(soup : OWNR, pivot : Object, ALL : Owner, SIN : Owner, FFO : Owner, FOP : Owner, FEP : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
  requires ALL == flownerAll(soup)
  requires SIN == flownerStrictlyInside(soup,pivot)
  requires FFO == flownerStrictlyOutside(soup,pivot)
  requires FOP == flownerOnlyPivot(soup,pivot)
  requires FEP == flownerExceptPivot(soup,pivot)
   ensures ALL == SIN + FFO + FOP + FEP
   ensures flownerAll(soup) == flownerStrictlyInside(soup,pivot) + flownerStrictlyOutside(soup,pivot) + (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))
{
  FLOWNER_ALL_ALL(soup, pivot);
}


lemma FLOWNER_DISJOINT(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()
   ensures flownerOnlyPivot(soup,pivot) !! flownerExceptPivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerOnlyPivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerExceptPivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerOnlyPivot(soup,pivot) !! flownerExceptPivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerOutsidePivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerOutsidePivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerStrictlyOutside(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot) + flownerStrictlyOutside(soup,pivot))
   ensures flownerStrictlyInside(soup,pivot) !! (flownerOutsidePivot(soup,pivot) + flownerStrictlyOutside(soup,pivot))
{}


lemma FLOWNER_CONJOINT(soup : OWNR, pivot : Object, FIO : Owner, FOP : Owner, FEP : Owner)
 //seems to be doing a fuckload of work to get fOutP == fOnlyP + fExceptP
  requires AllReady(flatten(soup)) && pivot.Ready()
  requires FOP == flownerOnlyPivot(soup,pivot)
  requires FEP == flownerExceptPivot(soup,pivot)
  requires FIO == flownerOutsidePivot(soup,pivot)
   ensures FIO == FOP + FEP
   ensures flownerOutsidePivot(soup,pivot) == (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))
{
   forall o <- soup, owner <- o.AMFO ensures (true) //by
     {
      PART_INSIDE_OWNER(soup,pivot);
      assert inside(o, owner);

      assert (owner in FOP) ==>  (owner in FIO);
      assert (owner in FEP) ==>  (owner in FIO);
      assert (owner in FIO) ==> ((owner in FOP) || (owner in FEP));
      assert (owner in FIO) ==> ((owner in FOP) != (owner in FEP));

      assert ownerOnlyPivot(o,pivot,owner)   ==>  pivotlyOutside(owner,pivot) && onlyPivot(o,pivot,owner);
      assert ownerExceptPivot(o,pivot,owner) ==>  pivotlyOutside(owner,pivot) && exceptPivot(o,pivot,owner);

      assert ownerOnlyPivot(o,pivot,owner)   <==  pivotlyOutside(owner,pivot) && onlyPivot(o,pivot,owner);
      assert ownerExceptPivot(o,pivot,owner) <==  pivotlyOutside(owner,pivot) && exceptPivot(o,pivot,owner);

      assert ownerOnlyPivot(o,pivot,owner)   <==> pivotlyOutside(owner,pivot) && onlyPivot(o,pivot,owner);
      assert ownerExceptPivot(o,pivot,owner) <==> pivotlyOutside(owner,pivot) && exceptPivot(o,pivot,owner);

      assert flownerOutsidePivot(soup,pivot) >= FIO;
      assert flownerOutsidePivot(soup,pivot) <= FIO;  //ERR

//      assert ownerOutsidePivot(o,pivot,owner) == outsidePivot(o,owner,pivot);

//      assert flownerOutsidePivot(soup,pivot) >= FIO;

     }
}




lemma FLOWNER_JOINT(soup : OWNR, pivot : Object, FIO : Owner, FOP : Owner, FEP : Owner)
 //delete in favour of FLOWNER_ALL_ALL?
  requires AllReady(flatten(soup)) && pivot.Ready()
  requires FOP == flownerOnlyPivot(soup,pivot)
  requires FEP == flownerExceptPivot(soup,pivot)
  requires FIO == flownerOutsidePivot(soup,pivot)
   ensures FIO == FOP + FEP
   ensures FOP !! FEP
{}



lemma FLOWNER_JOINT2(soup : OWNR, pivot : Object, FA : Owner, FB : Owner, FC : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
  requires FA == flownerAll(soup)
  requires FB == flownerStrictlyInside(soup,pivot)
  requires FC == flownerPivotlyOutside(soup,pivot)
   ensures FA == FB + FC
   ensures FB !! FC
{}


lemma FLOWNER_JOINT2x2(soup0 : OWNR, soup1 : OWNR, pivot : Object)
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
   ensures flownerStrictlyInside(soup0,pivot) !! flownerPivotlyOutside(soup0,pivot)
   ensures flownerStrictlyInside(soup1,pivot) !! flownerPivotlyOutside(soup1,pivot)
//   ensures flownerStrictlyInside(soup0,pivot) >= flownerStrictlyInside(soup1,pivot)
//   ensures flownerPivotlyOutside(soup0,pivot) >= flownerPivotlyOutside(soup1,pivot)
//   ensures (flownerStrictlyInside(soup0,pivot) + flownerStrictlyInside(soup1,pivot))
//    !! (flownerStrictlyInside(soup0,pivot) + flownerPivotlyOutside(soup1,pivot))
{}





///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////
//// random spare lemmers
////
////


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





lemma EXISTENTIAL_FUCKED(soup0 : Owner, soup1 : Owner, s : Object, pivot : Object, owner : Object, o : Object)
 //any ideas about wtf this does?
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flatten(soup0) >= flatten(soup1)


  requires stupidlyHappy(soup0, soup1, pivot)


  requires s in soup1
   ensures s in flatten(soup0)
  requires outside(s,pivot)
   ensures outside(s,pivot)

  requires owner in s.AMFO
   ensures inside(s,owner)
  requires owner in flatten(soup1)
   ensures owner in flatten(soup0)
  requires outside(owner,pivot)
   ensures outside(owner,pivot)

  requires s in o.AMFO

   ensures inside(o,s)
  requires o in soup0
   ensures o in flatten(soup0)
  // requires outside(o,pivot) //needs this to verify! --- either that or stupidlyHappy??
  //  ensures outside(o,pivot)

   requires forall q <- flatten(soup0) :: q.Ready()

  requires ownerStrictlyOutside(s,pivot,owner)
// ensures ownerStrictlyOutside(o,pivot,owner)   //neds o outside pivot to verify
   ensures (exists o <- soup0 :: (outside(o,pivot) && inside(o,s)))
   ensures (exists o <- soup0 |  (outside(o,pivot) && inside(o,s)) :: ownerStrictlyOutside(o,pivot,owner))   //but stupidlyHappy is enough if reframed comme ca


  {
    assert stupidlyHappy(soup0, soup1, pivot);
    assert (forall s <- soup1 | outside(s,pivot) :: exists o <- soup0 :: outside(o,pivot) && inside(o,s));
    assert s in soup1; assert outside(s,pivot);
    assert exists o <- soup0  :: outside(o,pivot) && inside(o,s);
    assert exists o <- soup0  :: (outside(o,pivot) && inside(o,s)) ==> ownerStrictlyOutside(o,pivot,owner);

    assert (forall r <- soup1 | outside(r,pivot) :: exists s <- soup0 :: outside(s,pivot) && inside(s,r));
    assert (exists o <- soup0  :: (outside(o,pivot) && inside(o,s)) ==> ownerStrictlyOutside(o,pivot,owner));
    assert (exists o <- soup0 | (outside(o,pivot) && inside(o,s)) :: ownerStrictlyOutside(o,pivot,owner));

  }




lemma ownerStrictlyOutside_OUTSIDE(o : Object, pivot : Object, owner : Object)
  requires o.Ready() && pivot.Ready() && owner.Ready()
  requires inside(o, owner)
  requires ownerStrictlyOutside(o,pivot,owner)
   ensures outside(owner,pivot)
   ensures outside(o,pivot)
{}




lemma SLUTTY(soup : Owner, pivot : Object, rv : Owner, other : Object, m : Klon)
 //verfies!!!his just an alternative "flatten" lemmer?
 // is t
  requires AllReady(flatten(soup)) && pivot.Ready() && AllReady(flatten(rv))
  requires flownerStrictlyInside(soup,pivot) == rv
  requires klonCalid(m)
   requires pivot == m.o

   ensures forall r <- rv :: r in flatten(soup)
   ensures forall r <- rv :: strictlyInside(r,pivot)
   ensures forall owner <- rv :: exists o <- soup | owner in o.AMFO ::
          (PART_INSIDE_OWNER(soup,pivot);  ownerStrictlyInside(o,pivot,owner))
   ensures forall r <- flatten(soup) | strictlyInside(r,pivot) :: r in rv

   requires other in flatten(soup)
   requires strictlyInside(other,pivot)
    ensures other in rv

   requires flatten(soup) <= m.m.Keys
{
 flownerStrictlyInside_RESULT(soup,pivot,rv);
 assert forall r <- flatten(soup) | strictlyInside(r,pivot) :: r in rv;
}
