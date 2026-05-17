//include "Ownership-Recursive.dfy"
include "Ownership-Parallel.dfy"



lemma fromTheManyOne(less : seq<nat>, more : seq<nat>)
   requires |less| == |more|
   requires forall x | 0 <= x < |less| :: less[x] <= more[x]
    ensures sum(less) <= sum(more)
    {}

function sum(s : seq<int>) : int
  { if (|s| == 0) then 0 else s[0] + sum(s[1..]) }



//
//
// lemma smooveOwnerator(divot : Owner, pivot : Owner, rivet : Owner, blivet : Owner, m : Klon)
//  //given that pivot is cloned to blivet
//  //lets see if partitioning owners across the pivot works
//    requires AllReady(divot)
//    requires AllReady(pivot)
//    requires AllReady(rivet)
//    requires AllReady(blivet)
//
//    requires klonReady(m)
//    requires klonCalid(m)
//
//    requires flatten(divot) >= flatten(pivot)
//    requires divot <= m.m.Keys
//    requires pivot <= m.m.Keys
//
//    requires mapThruKlon(divot, m) == rivet
//    requires mapThruKlon(pivot, m) == blivet
//
//     ensures flatten(rivet) >= flatten(blivet)
//
// {
//       assert klonCalid(m);
//       assert klonAllLines(m);
//
//
//       assert flatten(rivet) >= flatten(blivet);
// }
//











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
      assert divot.AMFO <= m.m.Keys;
      assert forall o <- divot.AMFO :: klonLine(o,m.m[o],m);
      assert mapThruKlon(divot.owner, m) == rivet.owner;

 var divotInside,divotOutside,divotFringe := splitOwnersAroundPivot(divot, pivot);
 assert pivot in divotFringe;
 var divotFringeNoPivot := divotFringe - {pivot};

 var rivetInside,rivetOutside,rivetFringe := splitOwnersAroundPivot(rivet, blivet);
 assert blivet in rivetFringe;
 var rivetFringeNoPivot := rivetFringe - {blivet};

assert forall o <- divotInside :: && (o in m.m.Keys);
assert forall o <- divotInside :: && (klonLine(o,m.m[o],m));

// assert forall o <- divotInside :: && (m.m[o] in rivetInside);  //ERR GRRR

assert divot.AMFO   >= pivot.AMFO;


assert forall d <- divotFringeNoPivot :: not(strictlyInside(d,pivot));
assert divotFringeNoPivot <= m.m.Keys;
assert forall d <- divotFringeNoPivot :: klonLine(d,m.m[d],m);
assert forall d <- divotFringeNoPivot :: m.m[d] == d;



// assert forall d <- divotFringeNoPivot :: d in rivetFringeNoPivot;  //ERR GRRR
// assert forall d <- rivetFringeNoPivot :: d in divotFringeNoPivot;  //ERR GRRR
//
// //  assert forall d <- divotInside :: m.m[d] in rivetInside;
//  assert divotFringeNoPivot == rivetFringeNoPivot;                   //ERR GRRR



}

//
// lemma KlonSplit(divot : Object, rivet : Object, m : Klon)
// //part is sstrictly inside pivot AND so is whole (sob)
//   requires part.Ready()
//   requires pivot.Ready()
//   requires whole.Ready()
//   requires strictlyInside(part, pivot)
//   requires strictlyInside(whole, pivot)
//   requires inside(part, whole)
// {
//    var partInside,partOutside,partFringe    := splitOwnersAroundPivot(part, pivot);
//    var wholeInside,wholeOutside,wholeFringe := splitOwnersAroundPivot(whole, pivot);
//
//    assert part.AMFO   >= whole.AMFO;
//    assert partInside  >= wholeInside;
//    assert partOutside >= wholeOutside;  //seems odd, but remember ?outside? is the upwarads closure of owners beyond the pivot.
//    assert partFringe  >= wholeFringe;
// }

lemma SuperSplit(part : Object, pivot : Object, whole : Object)
//part is sstrictly inside pivot AND so is whole (sob)
  requires part.Ready()
  requires pivot.Ready()
  requires whole.Ready()
  requires strictlyInside(part, pivot)
  requires strictlyInside(whole, pivot)
  requires inside(part, whole)
{
   var partInside,partOutside,partFringe    := splitOwnersAroundPivot(part, pivot);
   var wholeInside,wholeOutside,wholeFringe := splitOwnersAroundPivot(whole, pivot);

   assert part.AMFO   >= whole.AMFO;
   assert partInside  >= wholeInside;
   assert partOutside >= wholeOutside;  //seems odd, but remember ?outside? is the upwarads closure of owners beyond the pivot.
   assert partFringe  >= wholeFringe;
}


//
// lemma superJoin(part : Object, pivot : Object, whole : Object,
//                 partInside : Owner, partOutside : Owner, partFringe : Owner,
//                 wholeInside : Owner, wholeOutside : Owner, wholeFringe : Owner)
// ///likely unuseable, but...
//   requires part.Ready()
//   requires pivot.Ready()
//   requires whole.Ready()
//   requires AllReady(partInside)
//   requires AllReady(partOutside)
//   requires AllReady(partFringe)
//   requires AllReady(wholeInside)
//   requires AllReady(wholeOutside)
//   requires AllReady(wholeFringe)
//
//
//   requires strictlyInside(part, pivot)  //grr
//   requires strictlyInside(whole, pivot) //grr
//
//    ensures inside(part, whole) //note not strictly
// {}

lemma splitOwnersAroundPivot(part : Object, pivot : Object) returns (allInside : Owner, allOutside : Owner, fringe : Owner)
  //splits part.AMFO into the bits inside pivot,
  //the bits outside pivot,
  //and the fringe (bits outside that are direct owners of an owner inside...)
  //FUCK,. shoudl this be a function?  or indeed series of functions?
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
   ensures pivot in fringe
   ensures (fringe - {pivot}) == set x <- allInside, xo <- x.owner | (xo in allOutside) && (xo != pivot) :: xo
   ensures flatten(fringe - {pivot}) + flatten({pivot}) == flatten(fringe) == allOutside

   //ensures part.AMFO == recOwners(part)  //can do with Axioms from Ownership-Parallel if necessary...

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

  assert fringeNoPivot == set x <- allInside, xo <- x.owner | (xo in allOutside) && (xo != pivot) :: xo;

  assert (fringe - {pivot}) == set x <- allInside, xo <- x.owner | (xo in allOutside) && (xo != pivot) :: xo;
  assert flatten(fringe - {pivot}) + flatten({pivot}) == flatten(fringe) == allOutside;
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

lemma Flatten3(a : Owner, b : Owner, c : Owner)
  // requires AllReady(a)
  // requires AllReady(b)
  // requires AllReady(c)
  requires forall o <- a :: o.Ready()
  requires forall o <- b :: o.Ready()
  requires forall o <- c :: o.Ready()

    requires a + b == c
    ensures flatten(a) + flatten(b) == flatten(c)
    ensures flatten(a) + flatten(b) == flatten(a+b)
    ensures recFlatten(a)+recFlatten(b)==recFlatten(a+b)
    {}

lemma FLATTEN_SUMS(a : Owner, b : Owner, c : Owner, m : Klon)
   requires a+b == c
  // requires forall o <- a :: o.Ready()  //I'm OH SO TORY
  // requires forall o <- b :: o.Ready()  //I'm OH SO TORY
  // requires forall o <- c :: o.Ready()  //TORY TORY TORY
  //  requires AllReady(a)
  //  requires AllReady(b)
  //  requires AllReady(c)
  //  requires klonReady(m)
  //  requires klonCalid(m)
   requires (a+b+c) <= m.m.Keys
//    ensures recFlatten(a)+recFlatten(b)==recFlatten(a+b)
    ensures flatten(a) + flatten(b) == flatten(a+b)
    ensures mapThruKlon(a,m) + mapThruKlon(b,m) == mapThruKlon(a+b,m)
    ensures flatten(mapThruKlon(a,m)) + flatten(mapThruKlon(b,m)) == flatten(mapThruKlon(a+b,m))
   {}

lemma FLATTEN_ONE(o : Object)
 requires o.Ready()
 ensures flatten({o}) == {o} + flatten(o.owner) == o.AMFO
 {}


lemma {:timeLimit 20} MAPPEN_ONE(next : Object, m : Klon)
  requires next.Ready()
  requires next in m.m.Keys
  requires klonReady(m)
  requires klonCalid(m)
   ensures mapThruKlon({next},m) == {m.m[next]}
//   ensures flatten({next}) == {next} + flatten(next.owner)
//   ensures flatten(mapThruKlon(done+{next},m)) == flatten(mapThruKlon(done,m)) + flatten(mapThruKlon({next},m))
{
    FLATTEN_ONE(next);
//  assert mapThruKlon({next},m) == (set o <- {next} :: m.m[o]) == {m.m[next]};
}

lemma {:timeLimit 20} FLATTEN_TWO(done : Owner, next : Object, m : Klon)
  requires AllReady(done)
  requires next.Ready()
  requires klonReady(m)
  requires klonCalid(m)
  requires (done+{next}) <= m.m.Keys
   ensures (done+{next} == done + {next})
   ensures mapThruKlon(done+{next},m) == mapThruKlon(done,m) + mapThruKlon({next},m)
   ensures flatten(done+{next}) == flatten(done) + flatten({next})
   ensures flatten(mapThruKlon(done+{next},m)) == flatten(mapThruKlon(done,m)) + flatten(mapThruKlon({next},m))
{
  FLATTEN_SUMS(done,{next},done+{next},m);
}




lemma recSplatten(oo : Owner, m : Klon) returns (sp : Owner)
  decreases allAMFOs(oo)
   requires AllReady(oo)
   requires klonReady(m)
   requires klonCalid(m)
   requires oo <= m.m.Keys
//
//    requires |oo| == 1
//    requires forall o <- oo :: o.owner == {}
//     ensures flatten(oo) == oo

    ensures flatten(oo) <= m.m.Keys
    ensures sp == flatten(mapThruKlon(oo, m))
   {
//     var x :=  {set o : Object <- oo, ooo <- recOwners(o) :: ooo};

    sp := {};

    var todo := oo;
    var done : Owner := {};
    assert AllReady(todo);
    assert oo - todo == {};
    assert mapThruKlon({}, m) == {};
    assert mapThruKlon((oo - todo), m) == {};
    assert flatten({}) == {};
    assert flatten(mapThruKlon((oo - todo), m)) == {};

    assert sp == flatten(mapThruKlon((oo - todo), m));
    assert done == oo - todo == {};
    assert sp == flatten(mapThruKlon((done), m));

    while (todo > {})
        decreases todo
        invariant sp == flatten(mapThruKlon((oo - todo), m))
        invariant done == oo - todo
        invariant sp == flatten(mapThruKlon((done), m))
          {
            assert sp == flatten(mapThruKlon((oo - todo), m));
            var next :| next in todo;
            assert done == oo - todo;
            assert done + {next} == oo - (todo - {next});
            todo := todo - {next};
            assert done + {next} == oo - todo;

            var sext := m.m[next];
            assert klonLine(next, sext, m);
            assert klonIdentity(next, sext, m);

            var sowner;   var fowner;

            if (next == m.o)
              {
                assert sext == m.c;
                sowner := m.clowner;
                fowner := flatten(m.clowner);
                assert fowner == flatten(sext.owner);
              }
            else if (outside(next, m.o))
              {
                assert next == sext; assert next.owner == sext.owner;
                sowner := next.owner;
                fowner := flatten(next.owner);
                assert fowner == flatten(sext.owner);
              }
            else
              {
                assert strictlyInside(next, m.o);
                sowner := mapThruKlon(next.owner, m);
                assert sowner == sext.owner;
                fowner := recSplatten(next.owner, m);
                assert fowner == flatten(sext.owner);
              } //end if elseif else

            assert fowner == flatten(sext.owner);
            FLATTEN_ONE(sext);
            assert flatten({sext}) == ({sext} + flatten(sext.owner)) == ({sext} + fowner);
            MAPPEN_ONE(next,m);
            assert mapThruKlon({next}, m) == {m.m[next]} == {sext};
            assert flatten(mapThruKlon({next}, m)) == flatten({sext}) == ({sext} + fowner);
            assert sp == flatten(mapThruKlon((done), m));
            assert (done+{next}) == (done)+({next});    FLATTEN_SUMS(done,{next},done+{next},m);
            assert (mapThruKlon((done+{next}), m)) == (mapThruKlon((done), m)) + (mapThruKlon(({next}), m));
            assert flatten(mapThruKlon((done+{next}), m)) == flatten(mapThruKlon((done), m)) + flatten(mapThruKlon(({next}), m)) == sp + ({sext} + fowner);
            sp := sp + ({sext} + fowner);
            done := done + {next};
            assert done == oo - todo;
            assert sp == flatten(mapThruKlon((done), m));
            assert sp == flatten(mapThruKlon((oo - todo), m));
          }//end while
      assert sp == flatten(mapThruKlon((oo - todo), m));
      assert todo == {}; assert done == oo;
      assert sp == flatten(mapThruKlon(oo, m));
  }