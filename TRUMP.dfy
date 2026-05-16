include "Ownership-Recursive.dfy"



lemma fromTheManyOne(less : seq<nat>, more : seq<nat>)
   requires |less| == |more|
   requires forall x | 0 <= x < |less| :: less[x] <= more[x]
    ensures sum(less) <= sum(more)
    {}

function sum(s : seq<int>) : int
  { if (|s| == 0) then 0 else s[0] + sum(s[1..]) }


lemma smooveKlonerator(divot : Object, pivot : Object, rivet : Object, blivet : Object, m : Klon)
 //given that pivot is cloned to blivet
 //lets see if partitioning owners across the pivot works
   requires divot.Ready()
   requires pivot.Ready()
   requires rivet.Ready()
   requires blivet.Ready()

   requires klonReady(m)
   requires klonCalid(m)

   requires pivot  == m.o
   requires blivet == m.c



   requires strictlyInside(divot, pivot)
   requires m.objectInKlown(divot)
   requires m.m[pivot] == blivet   //is this too much already?
   requires m.m[divot] == rivet    //is this too much already already?

    ensures klonLine(divot,rivet,m)
    ensures strictlyInside(rivet, blivet)

{
      assert klonCalid(m);
      assert klonAllLines(m);
      assert klonLine(divot,rivet,m);
      assert strictlyInside(divot, pivot);
      assert divot != pivot;
      assert klonIdentity(divot,rivet,m);

      assert mapThruKlon(divot.owner, m) == rivet.owner;
}





lemma splitOwnersAroundPivot(part : Object, pivot : Object) returns (allInside : Owner, allOutside : Owner, fringe : Owner)
  //splits part.AMFO into the bits inside pivot,
  //the bits outside pivot,
  //and the fringe (bits outside that are direct owners of an owner inside...)
  requires part.Ready()
  requires pivot.Ready()
  requires strictlyInside(part, pivot)

   ensures AllReady(allInside)
   ensures AllReady(allOutside)
   ensures AllReady(fringe)

   ensures allInside  == set x <- part.AMFO | strictlyInside(x, pivot)
   ensures allOutside == set x <- part.AMFO | not(strictlyInside(x, pivot))
   ensures allInside !! allOutside
   ensures part.AMFO == (allInside + allOutside)
   ensures fringe == set x <- allInside, xo <- x.owner | (xo in allOutside)  :: xo
   ensures forall x <- fringe :: x in allOutside
   ensures flatten(fringe) == allOutside
  {
   var all := part.AMFO;

   allInside  := set x <- part.AMFO | strictlyInside(x, pivot);
   assert part in allInside;

   allOutside := part.AMFO - allInside;
   assert forall x <- allOutside :: not(strictlyInside(x, pivot));
   assert pivot in allOutside;

   assert forall x <- part.AMFO :: strictlyInside(x, pivot) != not(strictlyInside(x, pivot));

   assert allInside !! allOutside;
   assert all == (allInside + allOutside);

   fringe := set x <- part.AMFO, xo <- x.owner | (x in allInside) && (xo in allOutside)  :: xo;
   assert fringe <= allOutside;
   assert fringe == set x <- allInside, xo <- x.owner | (xo in allOutside)  :: xo;

   assert part !in fringe;
//   assert exists x <- allInside, xo <- x.owner ::  xo == pivot;

  var prev := YouGetThereEventually(part, pivot);
  assert pivot in prev.owner;
  assert strictlyInside(prev,pivot);
  assert prev in part.AMFO;
  assert inside(part,prev);
  assert prev in allInside;
  assert pivot in allOutside;
  assert pivot in fringe;

  assert flatten(fringe) <= allOutside;


  assert forall t <- allOutside :: inside(part, t);

  forall t <- allOutside ensures (t in flatten(fringe)) //(t in flatten(fringe))  //by
  {
      var prev, next := AcrossTheBorder(part, pivot, t);
      assert strictlyInside(prev,t);
      assert not(strictlyInside(next,pivot));
      assert prev in part.AMFO;
      assert next in prev.owner;
      assert prev in allInside;
      assert next in allOutside;
      assert next in fringe;
      assert t in part.AMFO;
      assert t in next.AMFO;
      assert t in flatten({next});
  }

  assert flatten(fringe) >= allOutside;
  assert flatten(fringe) == allOutside;

  var fringeNoPivot:= fringe - {pivot};
  assert pivot !in fringeNoPivot;

  var flatFringeNoPivot := flatten(fringeNoPivot);
  assert pivot !in flatFringeNoPivot;

  assert flatten(fringe - {pivot}) + flatten({pivot}) == flatten(fringe);
}




lemma AcrossTheBorder(part : Object,  pivot : Object, whole : Object) returns (prev : Object, next : Object)
  //returns transitive owners of part that on the way to whole, where prev is inside pivot, and next is outside or == pivot
 decreases part.AMFO
  requires part.Ready()
  requires whole.Ready()
  requires strictlyInside(part, whole)
  requires strictlyInside(part, pivot)
  requires not(strictlyInside(whole, pivot))

   ensures part != whole
   ensures prev in part.AMFO
   ensures next in part.AMFO
   ensures inside(part,prev)
   ensures strictlyInside(part,next)
   ensures strictlyInside(prev,pivot)
   ensures next in prev.owner
   ensures not(strictlyInside(next,pivot))
   ensures prev.Ready()
   ensures next.Ready()
   ensures whole in part.AMFO
   ensures whole in flatten({next})
   {
    prev := part;

    if (whole in prev.owner) {
        next := whole;
        return;
    }

    next := YouCan'tGetThereFromHereBut(prev, whole);

  //  assert part != whole;
  //  assert prev in part.AMFO;
  //  assert next in part.AMFO;
  //  assert next in prev.owner;
  //  assert inside(part,prev);
  //  assert strictlyInside(prev,;pivot);
  //  assert inside(next,whole));
  //  assert prev.Ready();
  //  assert next.Ready();

    while (strictlyInside(next,pivot))
      decreases next.AMFO
      invariant part != whole
      invariant prev in part.AMFO
      invariant next in part.AMFO
      invariant next in prev.owner
      invariant inside(part,prev)
      invariant strictlyInside(prev,pivot)
      invariant inside(next,whole)
      invariant prev.Ready()
      invariant next.Ready()
    {
      prev := next;
      next := YouCan'tGetThereFromHereBut(prev, whole);
    }

  //  assert part != whole;
  //  assert prev in part.AMFO;
  //  assert next in part.AMFO;
  //  assert next in prev.owner;
  //  assert inside(part,prev);
  //  assert strictlyInside(prev,pivot);
  //  assert not(strictlyInside(next,whole));
  //  assert prev.Ready();
  //  assert next.Ready();

   }




lemma YouGetThereEventually(part : Object, whole : Object) returns (prev : Object)
 //returns a (transitive) owner of part that is JUST BEFORE whole --- ie of which whole is a direct owner
 decreases part.AMFO
  requires part.Ready()
  requires whole.Ready()
  requires strictlyInside(part, whole)
   ensures part != whole
   ensures prev in part.AMFO
   ensures whole in prev.owner
   ensures strictlyInside(prev,whole)
   {
    if (whole in part.owner) {
        prev := part;
        assert prev in part.AMFO && whole in prev.owner;
        return;
    }
  assert whole !in part.owner;

    ThereIsALightThatNeverGoesOut(part, whole);
 //   assert (exists prev <- part.owner :: inside(prev, whole));

    prev := YouCan'tGetThereFromHereBut(part, whole);
    assert prev in part.owner;   assert whole !in part.owner;     assert prev != whole;
    assert inside(prev,whole);

    if (whole in prev.owner) {
        assert prev in part.AMFO && whole in prev.owner;
        return;
    }
    prev := YouGetThereEventually(prev, whole);
   }


// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // ////
/// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // ///


//
lemma {:timeLimit 30} ThereIsALightThatNeverGoesOut(part : Object, whole : Object)
  //at least one of part's direct owners is on the way to whole.
  requires part.Ready()
  requires whole.Ready()
  requires inside(part,whole)
  ensures (part == whole) || (exists x <- part.owner :: inside(x, whole))
 {
    InsideRecInside2(part, whole);

    if (part == whole) {
      assert ((part == whole) || (exists x <- part.owner :: inside(x, whole)));
      return; }

    assert part != whole;
    assert (exists x <- part.owner :: recInside(x,whole));
 }


ghost function {:isolate_assertions} YouCan'tGetThereFromHereBut(part : Object, whole : Object) : (next : Object)
  //return next - a "direct owner" of part that is on the way up to "whole"
 decreases part.AMFO

  requires part.Ready()
  requires whole.Ready()
  requires part != whole
  requires inside(part,whole)

   ensures next in part.owner
   ensures strictlyInside(part, next)
   ensures inside(next,whole)
   ensures (part.AMFO decreases to next.AMFO)
  {
    InsideRecInside2(part, whole);
    assert recInside(part, whole);
    ThereIsALightThatNeverGoesOut(part, whole);

    assert exists x <- part.owner :: inside(x, whole);

    var next : Object :| next in part.owner && inside(next, whole);

    assert part !in part.owner;
    assert next  in part.owner;
    assert part.AMFO > next.AMFO;
    assert (part.AMFO decreases to next.AMFO);
    assert inside(next,whole);

    next
  }










 //  ensures pivotlyOutside(part, whole) == not(strictlyInside(part, whole))

//    var allInside  := set x <- part.AMFO :: strictlyInside(x, whole);
//    var allOutside := set x <- part.AMFO :: pivotlyOutside(x, whole);
//
//    if (strictlyInside(part, whole))
//     {
//         assert pivotlyOutside(part, whole) == not(strictlyInside(part, whole)); return;
//     }
//
//   if (part == whole)
//     {
//         assert pivotlyOutside(part, whole) == not(strictlyInside(part, whole)); return;
//     }
//
//   assert not(strictlyInside(part, whole));
//   assert not(part.AMFO > whole.AMFO);
//   assert part != whole;
//   AXIOMAMFOS(part,whole);
//   assert part.AMFO != whole.AMFO;
//   assert not(part.AMFO >= whole.AMFO);
//   assert not(inside(part, whole));
//
//   assert pivotlyOutside(part, whole) == not(strictlyInside(part, whole));
