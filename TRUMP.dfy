include "Ownership-Parallel.dfy"



lemma allTRUMP(part : Object, whole : Object)
  //subdivides part.AMFO into the bits inside whole,
  //the bits outside whole, the fringe of the outside,
  //etc etc
  requires part.Ready()
  requires whole.Ready()
  requires strictlyInside(part, whole)
  {
   var all := part.AMFO;

   var allInside  := set x <- part.AMFO | strictlyInside(x, whole);
   assert part in allInside;

   // var allOutside := set x <- part.AMFO :: not(strictlyInside(x, whole));
   var allOutside := part.AMFO - allInside;
   assert forall x <- allOutside :: not(strictlyInside(x, whole));
   assert whole in allOutside;


   assert forall x <- part.AMFO :: strictlyInside(x, whole) != not(strictlyInside(x, whole));

   assert allInside !! allOutside;
   assert all == (allInside + allOutside);

   var toAndFro := set x <- part.AMFO, xo <- x.owner | (x in allInside) && (xo in allOutside)  :: xo;
   assert toAndFro <= allOutside;
   assert toAndFro == set x <- allInside, xo <- x.owner | (xo in allOutside)  :: xo;

   assert part !in toAndFro;
//   assert exists x <- allInside, xo <- x.owner ::  xo == whole;

  var prev := YouGetThereEventually(part, whole);
  assert whole in prev.owner;
  assert strictlyInside(prev,whole);
  assert prev in part.AMFO;
  assert inside(part,prev);
  assert prev in allInside;
  assert whole in allOutside;
  assert whole in toAndFro;

  assert flatten(toAndFro) <= allOutside;


  assert forall t <- allOutside :: inside(part, t);

  forall t <- allOutside ensures (t in flatten(toAndFro)) //(t in flatten(toAndFro))  //by
  {
      var prev, next := AcrossTheBorder(part, whole, t);
      assert strictlyInside(prev,t);
      assert not(strictlyInside(next,whole));
      assert prev in part.AMFO;
      assert next in prev.owner;
      assert prev in allInside;
      assert next in allOutside;
      assert next in toAndFro;
      assert t in part.AMFO;
      assert t in next.AMFO;
      assert t in flatten({next});
  }

  assert flatten(toAndFro) >= allOutside;

  var fringe := toAndFro - {whole};
  assert whole !in fringe;

  var flatFringe := flatten(fringe);
  assert whole !in flatFringe;



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