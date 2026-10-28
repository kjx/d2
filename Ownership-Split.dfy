include "Ownership.dfy"
include "Bound.dfy"

include "Ownership-Flatten.dfy" //be nice to remove this...

// 1. FlownerSpliut
// 2. Tertiary predicates ownerXX(o, pivot, owner)...
// 3. flowner functions, from a soup, via tertiary ownerXX predicates
// 4. nonflowner functions - collectStrictlyInside. collectOutsideAvoiding etc
///

// the stuff that does NOT depend on the Klon are doing the "horizontal" mapping
// between owner (bigger/deeper)  and  bound (smaller/shallower)
//
// actually, most of the code in this file is just about
// categorising owners of just one "soup"
// so the basis of that comparison, but not acutally doing it

// I think the ownerExceptPivot & friendsare wrongo.
// best attempt so far is at collectOutsideAvoiding - I think.
// does that really require constraints on soup0 side

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


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
    predicate {:timeLimit 60} Valid()
      {
      assume AllReady(flatten(soup));
      assume pivot.Ready();
    //  && AllReady(flatten(soup))   //should do better than that…
    //  && pivot.Ready() //…ditto
//pivot in     && (pivot in fAll) // makes ready work... - but how much else does it kill?
         ///HMM. doesn't this ban certainly null casses?  better to do this with m.m.Keys?
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


function {:timeLimit 10} flownerSplit(os : Owner,pivot : Object) : (rv : FlownerSplit)
  requires AllReady(flatten(os)) && pivot.Ready() ///PIVOTIN && (pivot in flatten(os))
   ensures flownerSplitOK(os, pivot, rv)
 {
  var fAll := flownerAll(os);
  var fSin := flownerStrictlyInside(os,pivot);
  var fOut := flownerStrictlyOutside(os,pivot);
  var fPvt := flownerOnlyPivot(os,pivot);
  var fXpt := flownerExceptPivot(os,pivot);
  FLOWNER_ALL_ALL(os,pivot);
  var fs := preFlownerSplit(os,pivot,fAll,fSin,fOut,fPvt,fXpt);
  assert fs.soup == os;
  assert fs.pivot == pivot;
  assert fs.Valid();
  assert flownerSplitOK(os, pivot, fs);
  fs
 }



predicate flownerSplitOK(soup : OWNR, pivot : Object, split : preFlownerSplit)
 // requires AllReady(soup) && pivot.Ready()
  {
      && (split.soup == soup)
      && (split.pivot == pivot)
      && (split.Valid())
  }


lemma UNPACK_flownerSplitOK(soup : OWNR, pivot : Object, split : FlownerSplit)
  requires AllReady(flatten(soup)) && pivot.Ready()
  requires split.soup  == soup
  requires split.pivot == pivot

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
{
  assert split.Valid();
}

// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
























///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////
//// Tertiary Pivot predicates
////
////
//the "o" here - likelt in the whole file - should be changed to "seed" or at least "s"

predicate outsidePivot(seed : Object, pivot : Object, owner : Object) : (rv : bool)   reads {}   { inside(seed, pivot) && inside(seed,owner) }
  //seed >= pivot is a selecwtion condition for this case
  //seed >= owner should be fucken built the fuck in

lemma LEMMA_outsidePivot(seed : Object, pivot : Object, owner : Object)
   requires inside(seed,owner)
    ensures outsidePivot(seed,pivot,owner) == inside(seed,pivot)
{}

predicate onlyPivot(seed : Object, pivot : Object, owner : Object) : (rv : bool)   reads {}   { inside(seed, pivot) && inside(seed,owner) &&  inside(pivot, owner) }
predicate exceptPivot(seed : Object, pivot : Object, owner : Object) : (rv : bool) reads {}   { inside(seed, pivot) && inside(seed,owner) && outside(pivot, owner) }
   //should we explicitly require owner in seed.AMFO  aka seed inside owner?
   //well apart from the "preconditions to the preconditions" problem



  //  ensures ( ||  (     inside(seed,pivot)       && strictlyInside(owner,pivot))  //ownerStrictlyInside
  //            ||  (  onlyPivot(seed,pivot,owner) && pivotlyOutside(owner,pivot))  //owner
  //            ||  (exceptPivot(seed,pivot,owner) && pivotlyOutside(owner,pivot))  //insife from outside not  pivot
  //            ||  (    outside(seed,pivot)       && outside(owner,pivot)) )       //fully outside

predicate ownerStrictlyInside(seed : Object, pivot : Object, owner : Object) : (rv : bool)
  requires seed.Ready() && pivot.Ready() && owner.Ready()  requires inside(seed, owner)  reads {}
    {strictlyInside(owner,pivot)}
predicate ownerInside(seed : Object, pivot : Object, owner : Object) : (rv : bool)
  requires seed.Ready() && pivot.Ready() && owner.Ready()  requires inside(seed, owner)  reads {}
    {inside(owner,pivot)}
predicate ownerPivotlyOutside(seed : Object, pivot : Object, owner : Object) : (rv : bool)
  requires seed.Ready() && pivot.Ready() && owner.Ready()  requires inside(seed, owner)  reads {}
    {pivotlyOutside(owner,pivot)}

predicate ownerStrictlyOutside(seed : Object, pivot : Object, owner : Object) : (rv : bool)
  requires seed.Ready() && pivot.Ready() && owner.Ready()  requires inside(seed, owner)  reads {}
    {outside(owner,pivot) &&  outside(seed,pivot)}
predicate ownerOutside(seed : Object, pivot : Object, owner : Object) : (rv : bool)
  requires seed.Ready() && pivot.Ready() && owner.Ready()  requires inside(seed, owner)  reads {}
    {outside(owner,pivot)}
predicate ownerOnlyPivot(seed : Object, pivot : Object, owner : Object) : (rv : bool)
  requires seed.Ready() && pivot.Ready() && owner.Ready()  requires inside(seed, owner)  reads {}
    {pivotlyOutside(owner,pivot) && onlyPivot(seed,pivot,owner)}
predicate ownerExceptPivot(seed : Object, pivot : Object, owner : Object) : (rv : bool)
  requires seed.Ready() && pivot.Ready() && owner.Ready()  requires inside(seed, owner)  reads {}
    {pivotlyOutside(owner,pivot) && exceptPivot(seed,pivot,owner)}
predicate ownerOutsidePivot(seed : Object, pivot : Object, owner : Object) : (rv : bool)
  requires seed.Ready() && pivot.Ready() && owner.Ready()  requires inside(seed, owner)  reads {}
    {pivotlyOutside(owner,pivot) && outsidePivot(seed,owner,pivot)}

predicate ownerDisjunctPivot(seed : Object, pivot : Object, owner : Object) : (rv : bool)
    requires seed.Ready() && pivot.Ready() && owner.Ready()  requires inside(seed, owner)  reads {}
        {ownerStrictlyOutside(seed,pivot,owner) || ownerExceptPivot(seed,pivot,owner)}
predicate ownerWithoutPivot(seed : Object, pivot : Object, owner : Object) : (rv : bool)
  requires seed.Ready() && pivot.Ready() && owner.Ready()  requires inside(seed, owner)  reads {}
    {outside(pivot,owner)}








///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////
//// "Flowner" functions - functions that flatten a "soup" into a set  divided in some why with a pivot
////
////

function flownerAll(soup : Owner) : OWNR {assume forall s <- soup :: s.Ready(); (set seed <- soup, oo <- seed.AMFO :: oo)}
  //yes same as flatten() etc...

function flownerStrictlyInside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set seed <- soup, owner <- seed.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerStrictlyInside(seed,pivot,owner) :: owner}
function flownerStrictlyOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set seed <- soup, owner <- seed.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerStrictlyOutside(seed,pivot,owner) :: owner}

function flownerInside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set seed <- soup, owner <- seed.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerInside(seed,pivot,owner) :: owner}
function flownerOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set seed <- soup, owner <- seed.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerOutside(seed,pivot,owner) :: owner}

function flownerOnlyPivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set seed <- soup, owner <- seed.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerOnlyPivot(seed,pivot,owner) :: owner}
function flownerExceptPivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set seed <- soup, owner <- seed.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerExceptPivot(seed,pivot,owner) :: owner}
function flownerOutsidePivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set seed <- soup, owner <- seed.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerOutsidePivot(seed,pivot,owner) :: owner}

function flownerDisjunctPivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set seed <- soup, owner <- seed.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerDisjunctPivot(seed,pivot,owner) :: owner}


 function flownerEverythingOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 { flownerStrictlyOutside(soup,pivot) + flownerOutsidePivot(soup,pivot) }
 function flownerPivotlyOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
   {set seed <- soup, owner <- seed.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerPivotlyOutside(seed,pivot,owner) :: owner}








///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////
//// Non - "Flowner" flattening functions - functions that flatten a "soup" into a set  divided in some why with a pivot
//// alternatives, often recursive
////


     //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //
    //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //
   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //
  //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //
 //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //
//   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //

///////// //////////// ///////// //////////// ///////// //////////// ///////// ////////////

predicate outsideAvoidingAlt(part : Object, whole : Object,  pivot : Object) : (rv : bool)
 // given part inside whole, is part outside pivot? AND is whole reachable NOT via the pivot
   decreases part.AMFO, 2
    requires part.Ready()
    requires whole.Ready()
    requires inside(part,whole)
     ensures outside(whole,pivot) <== rv
     ensures (part  == pivot) ==> not(rv)
     ensures (whole == pivot) ==> not(rv)
     ensures (part  == whole) ==> (outside(part,pivot) <==> rv)
      {whole in collectObjectOutsideAvoiding(part,pivot)}

predicate outsideAvoiding(part : Object, whole : Object,  pivot : Object) : (rv : bool)
 // given part inside whole, is part outside pivot? AND is whole reachable NOT via the pivot
   decreases part.AMFO, 2
    requires part.Ready()
    requires whole.Ready()
    requires inside(part,whole)
     ensures outside(whole,pivot) <== rv
   //  ensures not(outside(part,pivot))
     ensures (part  == pivot) ==> not(rv)
     ensures (whole == pivot) ==> not(rv)
     ensures (part  == whole) ==> (outside(part,pivot) <==> rv)
      { || (outside(part,pivot) && inside(part,whole))
        || (strictlyInside(part,pivot) && (exists oo <- part.owner :: (inside(oo,whole) && (outsideAvoiding(oo, whole, pivot)))))
      }


///////// //////////// ///////// //////////// ///////// //////////// ///////// ////////////

function collectOutsideAvoiding(soup : Owner, pivot : Object) : (rv : set<Object>)
///gets all outside owners - avoiding the pivot and any owners reachabke ONLY through that.
   decreases allAMFOs(soup), 2
   requires forall o <- soup :: o.Ready()
    ensures forall r <- rv :: outside(r,pivot)
    ensures forall r <- rv :: r in flatten(soup)
    { (set o <- soup, ooo <- collectObjectOutsideAvoiding(o,pivot) :: ooo) }

function collectObjectOutsideAvoiding(o : Object, pivot : Object) : (rv : set<Object>)
///gets all outside owners - avoiding the pivot and any owners reachabke ONLY through that.
  decreases o.AMFO, 1
   requires o.Ready()
    ensures forall r <- rv :: outside(r,pivot)
    ensures forall r <- rv :: r in o.AMFO
    { if (outside(o,pivot)) then (o.AMFO)
        else if (o == pivot) then ({})
          else (collectOutsideAvoiding(o.owner,pivot)) }
///////// //////////// ///////// //////////// ///////// //////////// ///////// ////////////
//
//  FOOKING 'ELL
//
// lemma {:timeLimit 10} FUCKER_ZUCKER(soup : Owner, pivot : Object, left : Owner, rite : Owner)
// //  decreases allAMFOs(soup), 2
//    requires forall o <- soup :: o.Ready()
//    requires pivot.Ready()
//    requires left == collectOwnerAvoiding(soup,pivot)
//    requires rite == (set o <- soup, ooo <- collectObjectOwnerAvoiding(o,pivot) :: ooo)
//
//     ensures left <= rite
//     ensures left >= rite
//     ensures left == rite
//     {
//       if (soup == {})
//         {
//           assert left == {};
//           assert rite == {};
//           assert left == rite;
//           return;
//         }
//
//       if (GroundSingleton(soup))
//         {
//           var consommee := ExtractFromSingleton(soup);
//           assert {consommee} == soup;
//           assert collectOwnerAvoiding({consommee},pivot) == left;
//           assert (set o <- {consommee}, ooo <- collectObjectOwnerAvoiding(o,pivot) :: ooo) == rite;
//
//           assert left == rite;
//           return;
//         }
//
// assert not(GroundSingleton(soup));
//       assert soup > {};
// //        var consommee :| (consommee in soup) && (soup decreases to {consommee});
//           var consommee :| (consommee in soup) && (allAMFOs(soup) decreases to allAMFOs({consommee}));
//           assert {consommee} <= soup;
//
// assert not(GroundSingleton(soup));
// assert (soup - {consommee}) > {};
// assert soup decreases to {consommee};
// assert allAMFOs(soup) > allAMFOs({consommee});
// assert allAMFOs(soup) decreases to allAMFOs({consommee});
//
//           var lift := collectOwnerAvoiding({consommee},pivot);
//           var ryte := (set o <- {consommee}, ooo <- collectObjectOwnerAvoiding(o,pivot) :: ooo);
//           assert ryte == (set ooo <- collectObjectOwnerAvoiding(consommee,pivot) :: ooo);
//           // assert ryte == (set o <- {consommee} ::
//           //     (set ooo <- collectObjectOwnerAvoiding(o,pivot) :: ooo));
//
//           assert forall o : Object <- {consommee} :: o.Ready();
//           assert pivot.Ready();
//           assert lift == collectOwnerAvoiding({consommee},pivot);
//           assert ryte == (set o <- {consommee}, ooo <- collectObjectOwnerAvoiding(o,pivot) :: ooo);
//          // FUCKER_ZUCKER({consommee}, pivot, lift, ryte);
//           assume lift == ryte;
//
//
//
//       assert left <= rite;
//     }
//
//
//
//     ensures collectOwnerAvoiding(soup,pivot) <= (set o <- soup, ooo <- collectObjectOwnerAvoiding(o,pivot) :: ooo)
//     ensures collectOwnerAvoiding(soup,pivot) >= (set o <- soup, ooo <- collectObjectOwnerAvoiding(o,pivot) :: ooo)
//     ensures collectOwnerAvoiding(soup,pivot) == (set o <- soup, ooo <- collectObjectOwnerAvoiding(o,pivot) :: ooo)


///the magic lines?
// assert forall oo <- soup :: (set ooo <- collectStrictlyInside({oo},pivot) :: ooo) == (set ooo <- flownerStrictlyInside({oo},pivot) :: ooo);
// assert (set oo <- soup, ooo <- (set x <- collectStrictlyInside({oo},pivot)) :: ooo) == (set oo <- soup, ooo <- flownerStrictlyInside({oo},pivot) :: ooo);
// assert (set oo <- soup, ooo <- collectStrictlyInside({oo},pivot) :: ooo) == (set oo <- soup, ooo <- flownerStrictlyInside({oo},pivot) :: ooo);
//




lemma {:timeLimit 10} FUCKER_WUCKER(owner : Object, soup : Owner, pivot : Object)
  decreases allAMFOs(soup), 2
   requires forall owner <- soup :: owner.Ready()
   requires AllReady(flatten(soup))
   requires pivot.Ready()
   requires owner in flatten(soup)
   requires outside(owner,pivot) //could be pivotly
    ensures owner  in flownerPivotlyOutside(soup, pivot)
    ensures owner  in flownerOutside(soup, pivot)
//    ensures owner  !in flownerOutsidePivot(soup,pivot)

   requires owner !in shortcutOnlyPivot(soup,pivot)
    ensures owner !in flattenOnlyPivot(soup,pivot)
    ensures owner !in flownerOnlyPivot(soup,pivot)
//    ensures owner  in flownerOutsidePivot(soup,pivot)
  //  ensures owner  in flownerExceptPivot(soup,pivot)
{
  var sOP := shortcutOnlyPivot(soup,pivot);
  assert owner !in sOP;
  ONLY_PIVOT(soup,pivot,sOP);
  FLOWNER_DISJOINT(soup, pivot);
  FLOWNER_CONJOINT(soup,pivot,
  flownerOutsidePivot(soup,pivot),
  flownerOnlyPivot(soup,pivot),
  flownerExceptPivot(soup,pivot));
  FLOWNER_JOINT(soup,pivot,
  flownerOutsidePivot(soup,pivot),
  flownerOnlyPivot(soup,pivot),
  flownerExceptPivot(soup,pivot));

   assert owner !in flownerOnlyPivot(soup,pivot);
   // assert owner  in flownerExceptPivot(soup,pivot); //ERR
}


lemma {:timeLimit 10} FUKKED_FUCKER(soup : Owner, pivot : Object)
  decreases allAMFOs(soup), 2
   requires forall o <- soup :: o.Ready()
   requires pivot.Ready()
   requires AllReady(flatten(soup))
   {

    forall seed <- soup, owner <- seed.AMFO ensures (true) //by
     {
       PART_INSIDE_OWNER(soup,pivot);
       assert ownerExceptPivot(seed,pivot,owner)  ==> not(ownerOnlyPivot(seed,pivot,owner));
      //  assert ownerExceptPivot(seed,pivot,owner) <==  not(ownerOnlyPivot(seed,pivot,owner));
//       assert ownerExceptPivot(seed,pivot,owner) <==> not(ownerOnlyPivot(seed,pivot,owner));
//       assert ownerExceptPivot(seed,pivot,owner)  !=      ownerOnlyPivot(seed,pivot,owner);



      //  assert ownerOutside(seed,pivot,owner)  ==> not(ownerOnlyPivot(seed,pivot,owner));
      // assert ownerOutside(seed,pivot,owner) <==  not(ownerOnlyPivot(seed,pivot,owner));


       assert ownerStrictlyOutside(seed,pivot,owner)  ==> not(ownerOnlyPivot(seed,pivot,owner));
      //  assert ownerStrictlyOutside(seed,pivot,owner) <==  not(ownerOnlyPivot(seed,pivot,owner));


      //  assert ownerOutsidePivot(seed,pivot,owner)  ==> not(ownerOnlyPivot(seed,pivot,owner));
      // assert ownerOutsidePivot(seed,pivot,owner) <==  not(ownerOnlyPivot(seed,pivot,owner));


      // assert ownerPivotlyOutside(seed,pivot,owner)  ==> not(ownerOnlyPivot(seed,pivot,owner));
      // assert ownerPivotlyOutside(seed,pivot,owner) <==  not(ownerOnlyPivot(seed,pivot,owner));

     }
   }

lemma {:timeLimit 10} HEY_FUCKER(soup : Owner, pivot : Object)
  decreases allAMFOs(soup), 2
   requires forall o <- soup :: o.Ready()
   requires pivot.Ready()
   requires AllReady(flatten(soup))
    ensures collectOutsideAvoiding(soup,pivot) + shortcutOnlyPivot(soup,pivot) <= flownerPivotlyOutside(soup,pivot)
   {
      var shortCut := shortcutOnlyPivot(soup,pivot);
      // LEMMA_shortcutOnlyPivot1(soup,pivot,shortCut);
      // assert forall r <- shortCut :: pivotlyOutside(r,pivot);
      // assert forall r <- shortCut :: r in flatten(soup);

      var maybePivot := if (pivot in flatten(soup)) then {pivot} else {};

     if (pivot in flatten(soup)) { assert maybePivot == {pivot}; }

      FLOWNER_SHORTCUT_OnlyPivot(soup,pivot,shortCut);
      ONLY_PIVOT(soup,pivot,shortCut);

      assert shortcutOnlyPivot(soup, pivot) == flattenOnlyPivot(soup, pivot) == flownerOnlyPivot(soup,pivot) ;

      assert                                      shortcutOnlyPivot(soup,pivot) <= flownerPivotlyOutside(soup,pivot);
      assert collectOutsideAvoiding(soup,pivot)                                 <= flownerPivotlyOutside(soup,pivot);
      assert collectOutsideAvoiding(soup,pivot) + shortcutOnlyPivot(soup,pivot) <= flownerPivotlyOutside(soup,pivot);

//    assert forall x <- flownerPivotlyOutside(soup,pivot) :: ((x == pivot) || outside(x,pivot));
      assert forall x <- flownerPivotlyOutside(soup,pivot) :: (pivotlyOutside(x,pivot));

      forall  x <- flownerPivotlyOutside(soup,pivot) ensures (x == pivot) || outside(x,pivot)
            {
                PIVOTLY_COME_OUTSIDE(x,pivot);
            }
//      assert forall x <- flownerPivotlyOutside(soup,pivot) :: not(strictlyInside(x,pivot));
 assert forall x <- flownerPivotlyOutside(soup,pivot) :: ((x == pivot) || outside(x,pivot));

  if (pivot in flatten(soup)) {
    assert pivot in shortcutOnlyPivot(soup,pivot);
    assert shortcutOnlyPivot(soup,pivot) == pivot.AMFO;
    assert pivot.AMFO <= flownerPivotlyOutside(soup,pivot);
    assert shortcutOnlyPivot(soup,pivot) <= flownerPivotlyOutside(soup,pivot);

        forall x <- flownerPivotlyOutside(soup,pivot) ensures (true)
          {

//              assert x in shortcutOnlyPivot(soup,pivot) + collectOutsideAvoiding(soup,pivot);

              if (x in pivot.AMFO) {
                assert (x in shortcutOnlyPivot(soup,pivot));
                  } else {
                assert pivotlyOutside(x,pivot);
                assert pivot in pivot.AMFO;
                assert x !in pivot.AMFO;
                assert x != pivot;
                assert outside(x,pivot);
                assert (x !in shortcutOnlyPivot(soup,pivot));
///                SET_SPLIT(x, shortcutOnlyPivot(soup,pivot), collectOutsideAvoiding(soup,pivot));
      //          assert (x in collectOutsideAvoiding(soup,pivot));
                  }
          }

  } else {
    assert (pivot !in flatten(soup));
    assert shortcutOnlyPivot(soup,pivot) == {};
  }

 assert (collectOutsideAvoiding(soup,pivot) + shortcutOnlyPivot(soup,pivot)) <= flownerPivotlyOutside(soup,pivot);

   }

      // forall x <- flownerPivotlyOutside(soup,pivot)
      //   ensures (
      //      || (x in collectOutsideAvoiding(soup,pivot))
      //      || (x in shortcutOnlyPivot(soup,pivot))
      //   )  {
      //     if (x !in collectOutsideAvoiding(soup,pivot))
      //       {
      //         assert x in flownerPivotlyOutside(soup,pivot);
      //         assert pivotlyOutside(x,pivot);
      //         if (x == pivot) { assert pivot in flownerPivotlyOutside(soup,pivot);
      //                           assert pivot in flownerAll(soup);
      //                           assert pivot in shortcutOnlyPivot(soup,pivot); }
      //                   else { assert x in flownerPivotlyOutside(soup,pivot);
      //                          assert pivotlyOutside(x,pivot);
      //                          assert x != pivot;
      //                          FUK_DA_POLICE(x,pivot);
      //                          assert outside(x,pivot);
      //                          assert x in flownerAll(soup);
      //                          assert x !in collectOutsideAvoiding(soup,pivot);
      //                          assert x in shortcutOnlyPivot(soup,pivot); }    //ERR ERR ERR ERR
      //         assert  (x in shortcutOnlyPivot(soup,pivot));
      //       }
      //   }

//BUGGER THIS - can we do this with preexiting definitions?



// if (pivot in flatten(soup))  {
//       assert maybePivot == {pivot};
//       assert shortcutOnlyPivot(soup,pivot) == pivot.AMFO;
//
//       assert collectOutsideAvoiding(soup,pivot) + shortcutOnlyPivot(soup,pivot) >= flownerPivotlyOutside(soup,pivot);
// } else {
//     assert pivot !in flatten(soup);
//     assert collectOutsideAvoiding(soup,pivot) + shortcutOnlyPivot(soup,pivot) >= flownerPivotlyOutside(soup,pivot);
//     assert maybePivot == {};
//     assert collectOutsideAvoiding(soup,pivot) + shortcutOnlyPivot(soup,pivot) >= flownerPivotlyOutside(soup,pivot);
//     assert collectOutsideAvoiding(soup,pivot) + shortcutOnlyPivot(soup,pivot) == flownerPivotlyOutside(soup,pivot);
// }


      // assert collectOutsideAvoiding(soup,pivot) + shortcutOnlyPivot(soup,pivot) == flownerPivotlyOutside(soup,pivot);

      // assert collectOutsideAvoiding(soup,pivot) + shortcutOnlyPivot(soup,pivot) == flownerPivotlyOutside(soup,pivot);
      // assert collectOutsideAvoiding(soup,pivot) + shortcutOnlyPivot(soup,pivot) == flownerPivotlyOutside(soup,pivot);






lemma AVOIDING_AVOIDANCE(part : Object, whole : Object,  pivot : Object)
  // outsideAvoiding == outsideAvoidingAlt
 //why clean your flat when you can AVOID IT ALL?
   decreases part.AMFO, 2
    requires part.Ready()
    requires whole.Ready()
    requires inside(part,whole)
     ensures outsideAvoiding(part,whole,pivot) == outsideAvoidingAlt(part,whole,pivot)
 {

    if ((part == pivot) || (whole == pivot))
    {
       assert not(outsideAvoiding(part,whole,pivot));
       assert not(outsideAvoidingAlt(part,whole,pivot));
       assert outsideAvoiding(part,whole,pivot) == outsideAvoidingAlt(part,whole,pivot);
       return;
    }

    if (part == whole) {

          assert outside(part,pivot) == outsideAvoiding(part,whole,pivot) == outsideAvoidingAlt(part,whole,pivot);
          return;
    }

    assert part != pivot;
    assert whole != pivot;
    assert whole != part;
    assert {part} !! {whole} !! {pivot};


    assert strictlyInside(part,whole);

    assert not((part == whole) &&    (outside(part,pivot)));    //defn outsideAvoiding
    assert     (part != whole) || not(outside(part,pivot));

    if (outside(part,pivot)) {
      assert outsideAvoiding(part,whole,pivot);
       assert collectObjectOutsideAvoiding(part,pivot) == part.AMFO;
       assert part in part.AMFO;
       assert whole in part.AMFO;
       assert outsideAvoidingAlt(part,whole,pivot);
       assert outsideAvoiding(part,whole,pivot) == outsideAvoidingAlt(part,whole,pivot);
       return;
    }

    if (inside(whole,pivot)) {
       assert forall r <- collectObjectOutsideAvoiding(part,pivot) :: outside(r,pivot);
       assert not(outsideAvoiding(part,whole,pivot));
       assert outsideAvoiding(part,whole,pivot) == outsideAvoidingAlt(part,whole,pivot);
       return;
    }

    assert strictlyInside(part,whole);
    assert inside(part,pivot);
    assert part != pivot;
    FUCKED_Inside_to_Strictly(part,pivot);
    assert strictlyInside(part,pivot);

    insideFUCKINGowner(part, whole);
    assert exists oo <- part.owner :: (part == whole) || (exists oo <- part.owner :: inside(oo,whole));
    assert exists oo <- part.owner :: (exists oo <- part.owner :: inside(oo,whole));

    forall oo <- part.owner | inside(oo,whole)  ensures (outsideAvoiding(oo,whole,pivot) == outsideAvoidingAlt(oo,whole,pivot))  {
        AVOIDING_AVOIDANCE(oo,whole,pivot);
//        assume outsideAvoiding(oo,whole,pivot) == outsideAvoidingAlt(oo,whole,pivot);   ///ASSUME FUCKED EVIL
          assert outsideAvoiding(oo,whole,pivot) == (whole in collectObjectOutsideAvoiding(oo,pivot));
        }

    assert forall oo <- part.owner |  inside(oo,whole)  :: outsideAvoiding(oo,whole,pivot) == outsideAvoidingAlt(oo,whole,pivot);


    if (outsideAvoiding(part,whole,pivot)) {
        assert  not(  outside(part,pivot) && inside(part,whole)  );
        assert strictlyInside(part,pivot);


        assert  whole in collectObjectOutsideAvoiding(part,pivot);

      assert outsideAvoiding(part,whole,pivot) == outsideAvoidingAlt(part,whole,pivot);
      return;
    }


    assert not( (outsideAvoiding(part,whole,pivot)) );


assert not(
        || (outside(part,pivot) && inside(part,whole))
        || (strictlyInside(part,pivot) && (exists oo <- part.owner :: (inside(oo,whole) && (outsideAvoiding(oo, whole, pivot)))))
);

assert strictlyInside(part,pivot);
assert not(outside(part,pivot) && inside(part,whole));
assert not(exists oo <- part.owner :: (inside(oo,whole) && (outsideAvoiding(oo, whole, pivot))));
assert forall oo <- part.owner :: not( (inside(oo,whole) && (outsideAvoiding(oo, whole, pivot))) );
assert forall oo <- part.owner :: not(inside(oo,whole))  ||  not(outsideAvoiding(oo, whole, pivot));

assert inside(whole,whole);
// assert not(outsideAvoiding(whole, whole, pivot));



    forall oo <- part.owner | inside(oo,whole)  ensures (outsideAvoiding(oo,whole,pivot) == (whole in collectObjectOutsideAvoiding(oo,pivot)))  {
        AVOIDING_AVOIDANCE(oo,whole,pivot);
//        assume outsideAvoiding(oo,whole,pivot) == outsideAvoidingAlt(oo,whole,pivot);   ///ASSUME FUCKED EVIL
          assert outsideAvoiding(oo,whole,pivot) == (whole in collectObjectOutsideAvoiding(oo,pivot));
        }


assert forall oo <- part.owner :: whole !in collectObjectOutsideAvoiding(oo,pivot);
assert whole != part;


//     assert not(outside(part,pivot) && inside(part,whole));
//     assert not (exists oo <- part.owner :: (inside(oo,whole) && (outsideAvoiding(oo, whole, pivot))));
//     assert forall oo <- part.owner :: not(inside(oo,whole) && (outsideAvoiding(oo, whole, pivot)));






    assert whole !in collectObjectOutsideAvoiding(part,pivot);
    assert not( (outsideAvoidingAlt(part,whole,pivot)) );
    assert outsideAvoiding(part,whole,pivot) == outsideAvoidingAlt(part,whole,pivot);

 }

    ///  CORRECT UP TO HERE!  CORRECT UP TO HERE!  CORRECT UP TO HERE!  CORRECT UP TO HERE!  CORRECT UP TO HERE!



lemma FUCKEDEDED(a : bool, b : bool)
   ensures not(a && b) == (not(a) || not(b))
   ensures not(a || b) == (not(a) && not(b))
{}

lemma FUCKinside(part : Object, whole : Object)
//    requires part.Ready() && whole.Ready()
     ensures inside(part,whole) == (part == whole) || (strictlyInside(part,whole))
{
  assume part.Ready() && whole.Ready();
}

lemma insideFUCKINGowner(part : Object, whole : Object)
 //
  requires part.Ready() && whole.Ready()
  requires inside(part,whole)
   ensures (part == whole) || (exists oo <- part.owner :: inside(oo,whole))
   {}

lemma FUCKED_Inside_to_Strictly(part : Object, whole : Object)
    requires inside(part,whole)
    requires part != whole
     ensures strictlyInside(part,whole)
     {
      assume part.Ready() && whole.Ready();
     }

///////// //////////// ///////// //////////// ///////// //////////// ///////// ////////////

function collectOwnerAvoiding(soup : Owner, pivot : Object) : (rv : set<Object>)
///gets all owners - inside & outsidem, avoiding the pivot and any owners reachabke ONLY through that.
   decreases allAMFOs(soup), 5
   requires forall o <- soup :: o.Ready()
    ensures forall r <- rv :: r in flatten(soup)
    ensures pivot !in rv
 //   ensures flatten(soup) >= rv >= (flatten(soup) - pivot.AMFO)
    { var rr :=  (set o <- soup, ooo <- collectObjectOwnerAvoiding(o,pivot) :: ooo)  ;
   //   MILLION_DOLLAR_DREAM(soup,pivot,rr) ;
    //  assert flatten(soup) >= rr >= (flatten(soup) - pivot.AMFO);
      rr}

function collectObjectOwnerAvoiding(o : Object, pivot : Object) : (rv : set<Object>)
///gets all owners - inside & outsidem, avoiding the pivot and any owners reachabke ONLY through that.
  decreases o.AMFO, 1
   requires o.Ready()
    ensures forall r <- rv :: r in o.AMFO
    ensures (o == pivot) ==> (rv == {})
    ensures pivot !in rv
//  ensures o.AMFO >= rv >= (o.AMFO - pivot.AMFO)
    { if (outside(o,pivot)) then (o.AMFO)
        else if (o == pivot) then ({})
          else ({o}+collectOwnerAvoiding(o.owner,pivot)) }


lemma MILLION_DOLLAR_DREAM(soup : Owner, pivot : Object, rv : set<Object>)
///gets all owners - inside & outsidem, avoiding the pivot and any owners reachabke ONLY through that.
   decreases allAMFOs(soup), 2
   requires forall o <- soup :: o.Ready()
   requires rv == collectOwnerAvoiding(soup,pivot)
    ensures forall r <- rv :: r in flatten(soup)
    ensures pivot !in rv
    ensures flatten(soup) >= rv >= (flatten(soup) - pivot.AMFO)
{
  forall o : Object <- soup
  //ERR vvvvvvvvvvvvvvvvvvv
     ensures flatten(soup) >= collectObjectOwnerAvoiding(o,pivot) >= (flatten(soup) - pivot.AMFO)
     {
      var rr := collectObjectOwnerAvoiding(o,pivot);
      TALLER_THAN_GOD(o,pivot,rr);
      assert o.AMFO >= rv >= (o.AMFO - pivot.AMFO);



      assert flatten(soup) >= rr;
      assert rr >= (flatten(soup) - pivot.AMFO);
     }
}

lemma SOUP_TO_NUTS(soup : Owner, pivot : Object, rv : set<Object>)
///gets all owners - inside & outsidem, avoiding the pivot and any owners reachabke ONLY through that.
   decreases allAMFOs(soup), 3
   requires forall o <- soup :: o.Ready()
   requires rv == collectOwnerAvoiding(soup,pivot)
   requires forall seed <- soup :: seed.AMFO >= collectObjectOwnerAvoiding(seed,pivot)
   requires forall seed <- soup :: collectObjectOwnerAvoiding(seed,pivot) >= (seed.AMFO - pivot.AMFO)
    ensures forall seed <- soup :: seed.AMFO >= collectObjectOwnerAvoiding(seed,pivot) >= (seed.AMFO - pivot.AMFO)

    ensures (set seed <- soup, ooo <- seed.AMFO :: ooo) == flatten(soup)

//    ensures flatten(soup) >= rv >= (flatten(soup) - pivot.AMFO)
{}

lemma SET_COMP_MINUS(soup : Owner, pivot : Object, rv : set<Object>)
   decreases allAMFOs(soup), 3
   requires forall o <- soup :: o.Ready()
   requires pivot.Ready()
    ensures (set seed <- soup, ooo <-  seed.AMFO :: ooo) == flatten(soup)
    ensures (set seed <- soup, ooo <- pivot.AMFO :: ooo) == pivot.AMFO

   requires rv == (set seed <- soup, ooo <- seed.AMFO :: ooo) - (set seed <- soup, ooo <- pivot.AMFO :: ooo)
    ensures rv == (set seed <- soup, ooo <- seed.AMFO :: ooo) - pivot.AMFO
    ensures rv == flatten(soup)                               - pivot.AMFO
{}



lemma MARR(soup : Owner, pivot : Object, rv : set<Object>)
   decreases allAMFOs(soup), 3
   requires forall o <- soup :: o.Ready()
   requires pivot.Ready()
   requires rv == (set seed <- soup, ooo <- pivot.AMFO :: ooo)
//    ensures rv == pivot.AMFO
  ensures SMALLTOWN_BOY(pivot,rv)
{
  if (soup == {}) {   assume SMALLTOWN_BOY(pivot,rv);
   return; }

  assume SMALLTOWN_BOY(pivot,rv);
}


lemma MORRISSEY(soup : Owner, pivot : Object, rv : set<Object>)
   decreases allAMFOs(soup), 3
   requires forall o <- soup :: o.Ready()
   requires pivot.Ready()
   requires rv == (set seed <- soup, ooo <- pivot.AMFO :: ooo)
    ensures (soup > {}) ==> (rv == pivot.AMFO)
    ensures (soup > {}) ==> SMALLTOWN_BOY(pivot,rv)
{
  if (soup == {}) { assert rv == {}; return; }

  assert soup > {};

  assert (set seed <- soup :: seed) == soup;

  assert (set seed <- soup :: pivot) == {pivot};
  assert (set seed <- soup :: pivot.AMFO) == {pivot.AMFO};
  assert (set ooo <- pivot.AMFO :: ooo) == pivot.AMFO;

  assert forall i <- rv :: i in pivot.AMFO;
  assert forall i <- pivot.AMFO :: i in rv;
     opaque {  //these two work non-opaquely
        assert rv == (set seed <- soup, ooo <- pivot.AMFO :: ooo);
        assert rv == pivot.AMFO;
     }
  assert SMALLTOWN_BOY(pivot,rv) by {
                                      reveal SMALLTOWN_BOY();
                                      assert rv == pivot.AMFO;
                                      assert SMALLTOWN_BOY(pivot,rv);
                                      }
}

opaque predicate SMALLTOWN_BOY(pivot : Object, rv : OWNR) {rv == pivot.AMFO}


lemma TALLER_THAN_GOD(o : Object, pivot : Object, rv : set<Object>)
///gets all owners - inside & outsidem, avoiding the pivot and any owners reachabke ONLY through that.
  decreases o.AMFO, 1
   requires o.Ready()
   requires rv == collectObjectOwnerAvoiding(o,pivot)

    ensures forall r <- rv :: r in o.AMFO
    ensures (o == pivot) ==> (rv == {})
    ensures pivot !in rv

    ensures o.AMFO >= rv
    ensures rv >= (o.AMFO - pivot.AMFO)
    ensures o.AMFO >= rv >= (o.AMFO - pivot.AMFO)

 { assume pivot.Ready();  assume forall r <- rv :: r.Ready();

    if (outside(o,pivot)) { assert rv == o.AMFO; assert rv >= (o.AMFO - pivot.AMFO); return; }

    assert inside(o,pivot);
    if (o == pivot)
         { assert o.AMFO == pivot.AMFO;
           assert o.AMFO -  pivot.AMFO == {};
           assert rv == {};
           assert rv >= (o.AMFO - pivot.AMFO);
           return; }

     assert strictlyInside(o,pivot);

     assert o in rv;
     var rr := collectOwnerAvoiding(o.owner,pivot);
     MILLION_DOLLAR_DREAM(o.owner,pivot,rr);
     assert flatten(o.owner) >= rr >= (flatten(o.owner) - pivot.AMFO);
    // assert o.AMFO >= rr >= (o.AMFO - pivot.AMFO);//ERR??
 }
///////// //////////// ///////// //////////// ///////// //////////// ///////// ////////////

function collectStrictlyInside(soup : Owner, pivot : Object) : (rv : set<Object>)
///version from BROWNE
  decreases allAMFOs(soup), 2
   requires forall o <- soup :: o.Ready()
    ensures forall r <- rv :: strictlyInside(r,pivot)
    ensures forall r <- rv :: r in flatten(soup)
    { (set o <- soup, ooo <- collectObjectStrictlyInside(o,pivot) :: ooo) }


function collectObjectStrictlyInside(o : Object, pivot : Object) : (rv : set<Object>)
///version from BROWNE
  decreases o.AMFO, 1
   requires o.Ready()
    ensures forall r <- rv :: strictlyInside(r,pivot)
    ensures forall r <- rv :: r in o.AMFO
    ensures rv <= argh(o)
    { if (not(strictlyInside(o,pivot))) then ({}) else ({o}+collectStrictlyInside(o.owner,pivot)) }


///////// //////////// ///////// //////////// ///////// //////////// ///////// ////////////

function flownerOutsideAvoiding(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); hackOwnerOutsideAvoiding(o,pivot,owner) :: owner}


predicate hackOwnerOutsideAvoiding(o : Object, pivot : Object, owner : Object)  : (rv : bool)
  decreases o.AMFO, 2
   requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    ensures rv ==> outside(owner,pivot)
      { owner in collectObjectOutsideAvoiding(o,pivot) }


lemma FUCKOTONIC(soup0 : Owner, soup1 : Owner, pivot : Object)
//I'm pretty fucking sure that XX avoiding anytihng avross the soup
//*isn't* monotiic, or fucktonic or any such thing.
//so this sholdh't verify and indeed it does not
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flatten(soup0) >= flatten(soup1)
///  ensures flownerOutsideAvoiding(soup0,pivot)  >= flownerOutsideAvoiding(soup1,pivot)
{
  assert soup1 <= flatten(soup1);
  assert soup1 <= flatten(soup0);
  assert forall s1 <- soup1 :: exists s0 <- soup0 :: s1 in s0.AMFO;
}

lemma DOWNWARDS_DOGE(down : Object, seed : Object, pivot : Object)
 decreases down.AMFO, 10
  requires down.Ready() && seed.Ready() && pivot.Ready()
  requires inside(down,seed)
  requires down != pivot //(I think I ned this or it all stops)
  requires outside(down,pivot)  //ths is overkill but should be enough!   /fuyck yeah
    //or does ot een fuckiong matter????
   ensures collectObjectOutsideAvoiding(down,pivot) >= collectObjectOutsideAvoiding(seed,pivot)
  {
    if (down == seed) { return; }

    if (seed == pivot)
      {
        assert collectObjectOutsideAvoiding(seed,pivot) == {};
        assert collectObjectOutsideAvoiding(down,pivot) >= collectObjectOutsideAvoiding(seed,pivot);
        return;
      }

    if (outside(seed,pivot))
      {
        assert collectObjectOutsideAvoiding(seed,pivot) == seed.AMFO;
        if (outside(down,pivot))
          {
            assert collectObjectOutsideAvoiding(down,pivot) == down.AMFO;
            assert strictlyInside(down,seed);
            assert collectObjectOutsideAvoiding(down,pivot) >= collectObjectOutsideAvoiding(seed,pivot);
            return;
           }

        assert inside(down,pivot);
          assert down != pivot;
          assert inside(down,seed);
          assert down != seed;
          assert exists do <- down.owner :: inside(do,seed);
          assert collectObjectOutsideAvoiding(down,pivot) == collectOutsideAvoiding(down.owner,pivot);
    assert inside(down,seed);
    assert exists do <- down.owner :: inside(do,seed);
    var do :| do in down.owner && inside(do,seed);  // can do = pivot??
     assert pivot !in seed.AMFO;
     assert do != pivot;
     assert inside(do,seed);
    DOWNWARDS_DOGE(do,seed,pivot);// by {  reveal CUNT; assert down != pivot; assert inside(down,seed); }
    assert collectObjectOutsideAvoiding(down,pivot) >= collectObjectOutsideAvoiding(seed,pivot);

         return;
      }

    assert strictlyInside(down,pivot);
    assert collectObjectOutsideAvoiding(down,pivot) == collectOutsideAvoiding(down.owner,pivot);

    assert inside(down,seed);
    assert exists do <- down.owner :: inside(do,seed);
    var do :| do in down.owner && inside(do,seed);
     assert do != pivot;
     assert inside(do, seed);
    DOWNWARDS_DOGE(do,seed,pivot);
    assert collectObjectOutsideAvoiding(down,pivot) >= collectObjectOutsideAvoiding(seed,pivot);
  }


lemma DOWNWARDS_ELON(down : Object, seed : Object, pivot : Object)
 decreases down.AMFO, 1
  requires down.Ready() && seed.Ready() && pivot.Ready()
  requires inside(down,seed)
  requires down != pivot //(I think I ned this or it all stops)
  requires down != seed //(options see above)
  requires outside(down,pivot)
  requires collectObjectOutsideAvoiding(down,pivot) == collectOutsideAvoiding(down.owner,pivot)
   ensures collectObjectOutsideAvoiding(down,pivot) >= collectObjectOutsideAvoiding(seed,pivot)
{
    assert inside(down,seed);
    assert exists do <- down.owner :: inside(do,seed);
    var do :| do in down.owner && inside(do,seed);
     assert CUNT: do != pivot;
     assert inside(do,seed);
    DOWNWARDS_DOGE(do,seed,pivot) by {  reveal CUNT; assert do != pivot; assert inside(do,seed); }
    assert collectObjectOutsideAvoiding(down,pivot) >= collectObjectOutsideAvoiding(seed,pivot);
}


     //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //
    //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //
   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //
  //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //
 //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //
//   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //   //





//
// predicate recOwnerOutsideAvoiding(o : Object, pivot : Object, owner : Object)  : (rv : bool)
//   decreases o.AMFO, 1
//    requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
//     ensures rv ==> outside(owner,pivot)
//     {  && outside(owner,pivot)
//        &&
//       if (outside(o,pivot)) then (o.AMFO)
//         else if (o == pivot) then ({})
//           else (collectOutsideAvoiding(o.owner,pivot)) }


lemma DUMBO(o : Object, pivot : Object)
  decreases o.AMFO, 1
   requires o.Ready() && pivot.Ready()
   requires outside(o,pivot)
    ensures forall oo <- o.AMFO :: outside(oo,pivot)
    {}




function arghStrictlyInside(o : Object, pivot : Object) : Owner
  decreases o.AMFO
   requires o.Ready()
 { allStrictlyInside(argh(o), pivot) }


//
// function collectObjectStrictlyInside(o : Object, pivot : Object) : (rv : set<Object>)
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
//     { assume forall o <- soup :: o.Ready(); (set o <- soup, ooo <- collectObjectStrictlyInside(o,pivot) :: ooo) }
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
   ensures forall r <- rv :: r in flatten(soup)
  ensures forall r <- rv :: strictlyInside(r,pivot)
  //  ensures forall owner <- rv :: exists o <- soup | owner in o.AMFO ::
  //         (PART_INSIDE_OWNER(soup,pivot);  ownerStrictlyInside(o,pivot,owner))
{
  if (soup == {}) {return;}

  forall oo <- soup ensures (true) {
    var rs := collectObjectStrictlyInside(oo, pivot);
    assert (oo in rs) ==> strictlyInside(oo,pivot);
    collectStrictlyInside_RESULT(oo.owner,pivot, collectStrictlyInside(oo.owner,pivot) );
  // assert rs == if (strictlyInside(oo,pivot)) then {oo} + collectStrictlyInside(oo.owner, pivot) else {};
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
   ensures (pivot  in flatten(soup))  ==> (rv == pivot.AMFO)
   ensures (pivot !in flatten(soup)) ==> (rv == {})
   ensures rv == (if (pivot in flatten(soup)) then (pivot.AMFO) else {})
   ensures shortcutOnlyPivot(soup, pivot) == rv
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

  requires stupidlyHappy(soup0, soup1, pivot)

  requires flownerAll(soup0) >= flownerAll(soup1)
  requires flatten(soup0) >= flatten(soup1)

   ensures flownerStrictlyInside(soup0,pivot)    >= flownerStrictlyInside(soup1,pivot)
  // ensures flownerStrictlyOutside(soup0,pivot)   >= flownerStrictlyOutside(soup1,pivot)
   ensures flownerOnlyPivot(soup0,pivot)         >= flownerOnlyPivot(soup1,pivot)
   ensures flownerExceptPivot(soup0,pivot)       >= flownerExceptPivot(soup1,pivot)
   ensures flownerOutsidePivot(soup0,pivot)      >= flownerOutsidePivot(soup1,pivot)
   ensures flownerEverythingOutside(soup0,pivot) >= flownerEverythingOutside(soup1,pivot)
   ensures flownerPivotlyOutside(soup0,pivot)    >= flownerPivotlyOutside(soup1,pivot)

//   ensures flownerOutsideAvoiding(soup0,pivot) >= flownerOutsideAvoiding(soup1,pivot)
//   ensures collectOutsideAvoiding(soup0,pivot) >= collectOutsideAvoiding(soup1,pivot)
 //  ensures flownerDisjunctPivot(soup0,pivot)     >= flownerDisjunctPivot(soup1,pivot)
{
    flownerStrictlyInside_MONOTONIC(soup0, soup1, pivot);
//    flownerStrictlyOutside_MONOTONIC(soup0, soup1, pivot);
    flownerOnlyPivot_MONOTONIC(soup0, soup1, pivot);
    flownerExceptPivot_MONOTONIC(soup0, soup1, pivot);
    flownerOutsidePivot_MONOTONIC(soup0, soup1, pivot);
  //  flownerPivotlyOutside_MONOTONIC(soup0, soup1, pivot);
 //   flownerOutsideAvoiding_MONOTONIC(soup0, soup1, pivot);
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


lemma flownerAll_SONOMONIC_AND_HAPPY_AND_BOUNDS(xo : Owner, xo_sp : (FlownerSplit), xb : Owner, xb_sp : FlownerSplit, pivot : Object)
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

lemma {:timeLimit 30} flownerStrictlyInside_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
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
  requires stupidlyHappy(soup0,soup1,pivot)

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

  requires stupidlyHappy(soup0,soup1,pivot)

   ensures flownerOutsidePivot(soup0,pivot)  >= flownerOutsidePivot(soup1,pivot)
   ensures flownerOutside(soup0,pivot) >= flownerOutside(soup1,pivot)
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



///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////
//// "shortcut" defintions & lemmas
////  basically recursive alternatives?
////




lemma FUK_DA_POLICE(x : Object, pivot : Object)
  requires pivotlyOutside(x,pivot)
  requires x != pivot
   ensures outside(x,pivot)
{
  assert pivotlyOutside(x,pivot);
  assert not(strictlyInside(x,pivot));
  STRICTLY_COME_INSIDE(x,pivot);
  assert outside(x,pivot) || (x == pivot);
  assert outside(x,pivot);
}





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




lemma {:timeLimit 16} GOOLE(o : Object, pivot : Object)
  requires o.Ready() && pivot.Ready()

   ensures shortcutOnlyPivot({o},pivot) <= o.AMFO
   ensures collectObjectOutsideAvoiding(o,pivot) <= o.AMFO
   ensures collectObjectOwnerAvoiding(o,pivot) <= o.AMFO
   ensures collectObjectStrictlyInside(o,pivot) <= o.AMFO

  //  ensures (shortcutOnlyPivot({o},pivot) + collectObjectOwnerAvoiding(o,pivot)) <= o.AMFO
  //  ensures (shortcutOnlyPivot({o},pivot) + collectObjectOwnerAvoiding(o,pivot)) >= o.AMFO
   ensures (shortcutOnlyPivot({o},pivot) + collectObjectOwnerAvoiding(o,pivot)) == o.AMFO
{
  if (o.owner == {})  { return; }

  assert o.owner > {};

  if (outside(o,pivot))  { return; }

  assert  (inside(o,pivot));

  assert {o} > {};
  assert (exists s <- {o} :: inside(s,pivot));
  assert shortcutOnlyPivot({o},pivot) == pivot.AMFO;


  assert  (shortcutOnlyPivot({o},pivot) + collectObjectOwnerAvoiding(o,pivot)) == o.AMFO;
}

lemma {:timeLimit 16} HULL(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()

   ensures shortcutOnlyPivot(soup,pivot) <= flatten(soup)
   ensures collectOutsideAvoiding(soup,pivot) <= flatten(soup)
   ensures collectOwnerAvoiding(soup,pivot) <= flatten(soup)
   ensures collectStrictlyInside(soup,pivot) <= flatten(soup)

   ensures (shortcutOnlyPivot(soup,pivot) + collectOwnerAvoiding(soup,pivot)) <= flatten(soup)
 //  ensures (shortcutOnlyPivot(soup,pivot) + collectOwnerAvoiding(soup,pivot)) >= flatten(soup)
{
   var rv := flownerOnlyPivot(soup,pivot);
   assert AllReady(flatten(rv));
   flownerOnlyPivot_RESULT(soup,pivot,rv);
   assert rv == shortcutOnlyPivot(soup,pivot);

   assert rv == if (pivot in flatten(soup)) then (pivot.AMFO) else {};

   if (pivot !in flatten(soup)) {
      assert shortcutOnlyPivot(soup,pivot) == {};
      assert forall o <- flatten(soup) :: o.AMFO <= flatten(soup);
      assert forall o <- flatten(soup) :: pivot !in o.AMFO;
      assert forall o <- flatten(soup) :: outside(o,pivot);
      assert forall o <- flatten(soup) | o != pivot :: collectObjectOwnerAvoiding(o,pivot) == o.AMFO;
      assert (pivot !in flatten(soup)) ==> forall o <- flatten(soup) :: o != pivot;
      assert forall o <- flatten(soup) :: o != pivot;
      assert forall o <- flatten(soup) | (o != pivot) :: (collectObjectOwnerAvoiding(o,pivot) == o.AMFO);


      assert forall o <- flatten(soup) | o != pivot :: collectObjectOwnerAvoiding(o,pivot) == o.AMFO;

      assert collectOwnerAvoiding(soup,pivot) == (set o <- soup, ooo <- collectObjectOwnerAvoiding(o,pivot) :: ooo);

      assert collectOwnerAvoiding(soup,pivot) == (set o <- soup, ooo <- o.AMFO :: ooo);
      assert collectOwnerAvoiding(soup,pivot) == flatten(soup);
   }
}



lemma {:timeLimit 6} ONLY_PIVOT(soup : OWNR, pivot : Object, rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()

  requires || (flownerOnlyPivot(soup,pivot) == rv)
           || (flattenOnlyPivot(soup,pivot) == rv)
           || (shortcutOnlyPivot(soup,pivot) == rv)

   ensures ((pivot  in flownerAll(soup)) ==> (rv == pivot.AMFO))
   ensures ((pivot  in flatten(soup))  ==> (rv == pivot.AMFO))

   ensures ((pivot !in flownerAll(soup)) && (pivot !in flatten(soup)))  ==> (rv == {})

   ensures shortcutOnlyPivot(soup, pivot) == flattenOnlyPivot(soup, pivot) == flownerOnlyPivot(soup,pivot) == rv
 {
   assume AllReady(flatten(soup));
   assume pivot.Ready();

if (shortcutOnlyPivot(soup,pivot) == rv)
     {
     LEMMA_shortcutVSflatten2(soup, pivot, shortcutOnlyPivot(soup, pivot), flattenOnlyPivot(soup, pivot));
     FLOWNER_FLATTEN_TODO_FOR_ALL(soup,pivot);
     return;
      }

if (flattenOnlyPivot(soup,pivot) == rv)
  {
    LEMMA_shortcutVSflatten2(soup, pivot, shortcutOnlyPivot(soup, pivot), flattenOnlyPivot(soup, pivot));
    FLOWNER_FLATTEN_TODO_FOR_ALL(soup,pivot);
    return;
  }

if (flownerOnlyPivot(soup,pivot) == rv)
  {
   flownerOnlyPivot_RESULT(soup,pivot,rv);
   return;
  }

assert false;

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




lemma {:timeLimit 30} FLOWNER_ALL_ALL(soup : OWNR, pivot : Object)
//can be replaced with split.Valid()
 //verified 20 Sep 2026 / 27 Oct 2026
  requires AllReady(flatten(soup)) && pivot.Ready()  //GOTTA GET RIDDA THIS SHITE
  requires AllReady(soup)
  requires forall seed <- soup :: seed.Ready()

   ensures flownerAll(soup) == flownerStrictlyInside(soup,pivot) + flownerStrictlyOutside(soup,pivot) + flownerOutsidePivot(soup,pivot)
   ensures flownerOutsidePivot(soup,pivot) == (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))

   ensures flownerAll(soup) == flownerStrictlyInside(soup,pivot) +  flownerStrictlyOutside(soup,pivot) + (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))
   ensures flownerAll(soup) == flownerStrictlyInside(soup,pivot) +  flownerPivotlyOutside(soup,pivot)

   ensures                     flownerStrictlyInside(soup,pivot) !! (flownerStrictlyOutside(soup,pivot) + flownerOutsidePivot(soup,pivot))
   ensures                     flownerStrictlyInside(soup,pivot) !! flownerPivotlyOutside(soup,pivot)

   ensures flownerEverythingOutside(soup,pivot) == flownerStrictlyOutside(soup,pivot) + flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot)
   ensures flownerPivotlyOutside(soup,pivot) == flownerStrictlyOutside(soup,pivot) + flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot)
{}





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
      assert flownerOutsidePivot(soup,pivot) <= FIO;

//      assert ownerOutsidePivot(o,pivot,owner) == outsidePivot(o,owner,pivot);

//      assert flownerOutsidePivot(soup,pivot) >= FIO;

     }
}






lemma SET_SPLIT(o : Object, a : Owner, b : Owner)
  requires o in (a + b)
  requires o !in a
   ensures o in b
{}

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


predicate split01(s0 : FlownerSplit, s1 : FlownerSplit) : (rv : bool)
   {
      && (s0.Valid())
      && (s1.Valid())
      && (s0.pivot == s1.pivot)
      && (s0.fAll >= s1.fAll)   //flattened all
   }

lemma YBOUNDEN(s0 : FlownerSplit, s1 : FlownerSplit)
   requires AllReady(s0.fAll)
   requires AllReady(s1.fAll)
   requires s0.pivot.Ready()
   requires s1.pivot.Ready()
   requires split01(s0,s1)
   requires stupidlyHappy(s0.soup, s1.soup, s0.pivot)
    ensures (s0.fSin >= s1.fSin)   //flownerStrictlyInside
//  ensures (s0.fOut >= s1.fOut)   //flownerStrictlyOutside - GRRR
    ensures (s0.fPvt >= s1.fPvt)   //flownerOnlyPivot
    ensures (s0.fXpt >= s1.fXpt)   //flownerExceptPivot

{
    UNPACK_flownerSplitOK(s0.soup,s0.pivot,s0);
    UNPACK_flownerSplitOK(s1.soup,s1.pivot,s1);
    flownerAll_MONOTONIC(s0.soup,s1.soup,s0.pivot);
}
