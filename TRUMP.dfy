//include "Ownership-Recursive.dfy"
include "Ownership-Parallel.dfy"


lemma SETIN(left : Owner, right : Owner)
  requires forall f <- left :: f in right
   ensures left <= right
{}

lemma SETLREQ(left : Owner, right : Owner)
  requires left <= right
  requires left >= right
   ensures left == right
{}

//{:timeLimit 30} {:timeLimit 60}
lemma cartography(owner : Owner, pivot : Object)
//topology?  enfringement?  whatevs?
  returns (owners_inside : Owner, owners_outside : Owner, flat_below : Owner, fringe : Owner)

 requires AllReady(flatten(owner))
 requires pivot.Ready()     requires piR: pivot.Ready()

  ensures owners_inside  == set x <- owner |  inside(x, pivot)
  ensures owners_outside == set x <- owner | outside(x, pivot)
  ensures owner == owners_outside + owners_inside
  ensures flatten(owner) == flatten(owners_inside) + flatten(owners_outside)

  ensures flat_below == set x <- flatten(owners_inside) | inside(x,pivot)
  ensures fringe     == set x <- flatten(owners_inside), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo

  ensures reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe)
  ensures flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot)

  ensures owners_inside <= flat_below
  ensures flat_below <= flatten(owners_inside)

{
  makerfield(owner,pivot);
  owners_inside  := set x <- owner |  inside(x, pivot);
  owners_outside := set x <- owner | outside(x, pivot);
  assert FLOOI: flatten(owner) == flatten(owners_outside) + flatten(owners_inside);

// //////////////////////////////////////////////////////////////////////////////////////////////////////////
//   assert flatten(owner) == flatten(owners_outside) + flatten(owners_inside);
//   assert flatten(owners_outside) == flatten(set x <- owner | outside(x, pivot));
//   assert flatten(owners_inside) == flat_inside_nopivot + pflivot(owner, pivot);
//   assert flat_inside_nopivot == flat_below + flat_above;
//   assert flatten(owners_inside) ==
//   assert flat_above == flatten(whole_f) == flatten(fringe) + flatten(pivot_f)
//   assert flat_below ==
//
//   assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot);
//   assert reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
//   return;
//////////////////////////////////////////////////////////////////////////////////////////////////////////



  if (owners_inside == {})
  {
    flat_below := {}; fringe := {};
    assert owners_outside == owner;

    assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot);
    assert reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
    return;
  }


  if (owners_inside == {pivot})
  {
    flat_below := {pivot}; fringe := {};
    assert owners_outside == owner - {pivot};

    assert flat_below == {pivot};
    assert flatten(fringe) == {};
    assert flatten(owner) == flatten(owners_outside) + {pivot} + {} + pflivot(owner, pivot);

    assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot);
    assert reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
    return;
  }

//the pivot MAY be within owners_inside - but only if it's in the actual "owner" argument
//otherwise the pivot won't be in owners_inside
//BUT: the pivot (and its flattening) most certainly will be in flatten(owners_inside)
//because every one or the owners_inside is inside the pivot (by definiton)



  assert flatten(owners_outside) == flatten(set x <- owner | outside(x, pivot));

  assert owners_inside > {};

  assert exists o <- owners_inside :: strictlyInside(o,pivot);

  var owners_inside_nopivot := owners_inside - {pivot};
  assert owners_inside_nopivot > {};  //implied by strictlyInside above

  if (pivot in owner) {
    assert pivot in owners_inside;
    assert owners_inside_nopivot + {pivot} == owners_inside;
    FLATTEN_SUM3(owners_inside_nopivot, {pivot}, owners_inside);
    assert flatten(owners_inside_nopivot) + flatten({pivot}) == flatten(owners_inside);
    assert pflivot(owner, pivot) == flatten({pivot});
    assert flatten(owners_inside_nopivot) + pflivot(owner, pivot) == flatten(owners_inside);
  }
  else
  {
    assert pivot !in owners_inside;
    assert owners_inside_nopivot == owners_inside;
    assert flatten(owners_inside_nopivot) + {} == flatten(owners_inside);
    assert pflivot(owner, pivot) == {};
    assert flatten(owners_inside_nopivot) + pflivot(owner, pivot) == flatten(owners_inside);
  }

    assert flatten(owners_inside) == flatten(owners_inside_nopivot) + pflivot(owner, pivot);


  var flat_inside_nopivot := flatten(owners_inside_nopivot);
   assert pivot in flat_inside_nopivot;
   FlattenContainsFlatten(owners_inside_nopivot,{pivot});
   assert flatten({pivot}) <= flat_inside_nopivot;    ///yes but htis pivot stems from one of the owners_inside_nopivot --- not pivot itself listed seperately
    assert flatten(owners_inside) == flat_inside_nopivot + pflivot(owner, pivot);


      flat_below := set x <- flat_inside_nopivot | inside(x,pivot);   ///pivot will be inside
  var flat_above := set x <- flat_inside_nopivot | outside(x,pivot);  //do I need this one?
  makerfield(flat_inside_nopivot,pivot);
  assert flat_inside_nopivot == flat_below + flat_above;


var whole_f;
var pivot_f;

//do I ned this call here - or can I just convert the following asserts into assignments?
whole_f,fringe,pivot_f := GordonRamseyThemFringes(owners_inside_nopivot, pivot);
// perhaops better to turn this around, have the definitions here,
//   and the pass them into as lemma, rather than getting them out of the lemma?


//jun05 2026
// assert   whole_f  == set x  <- flat_inside_nopivot, xo <- x.owner |                  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
// assert   fringe   == set x  <- flat_inside_nopivot, xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
// assert   pivot_f  == set x  <- flat_inside_nopivot, xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
 assert  forall x <- flat_inside_nopivot |  inside(x,pivot)  :: x in flat_below;
assert  forall x <- flat_below :: (x in  flat_inside_nopivot) && inside(x,pivot);

// assert (set x <- flat_below) == (set x <- flat_inside_nopivot |  inside(x,pivot));
//
// assert   whole_f  == set x : Object <- flat_below, xo <- x.owner  |                                     && (outside(xo,pivot) ) :: xo;
// assert   fringe   == set x : Object <- flat_below, xo <- x.owner  | (x != pivot)                        && (outside(xo,pivot) ) :: xo;
// assert   pivot_f  == set x : Object <- flat_below, xo <- x.owner  | (x == pivot)                        && (outside(xo,pivot) ) :: xo;

assert pivot_f + fringe == whole_f;
FLATTEN_SUM3(pivot_f,fringe,whole_f);
assert flatten(pivot_f) + flatten(fringe) == flatten(whole_f);
assert pivot_f == pivot.owner;   assert PIVOT_FO: pivot_f == pivot.owner;


// assert flatten(whole_f)  == flat_above;

assert forall w <- whole_f :: outside(w,pivot);

  forall t <- flat_above ensures (t in (flatten(fringe) + flatten(pivot_f)))   // (t in flatten(fringe)) //(t in flatten(fringe))  //by
  {
    forall part <- owners_inside_nopivot | (t in flatten({part})) ensures (t in (flatten(fringe) + flatten(pivot_f))) {
      var prev, next := AcrossTheBorder(part, pivot, t);
      assert strictlyInside(prev,t);
      assert not(strictlyInside(next,pivot)); //ORIG
      assert prev in flatten(owners_inside_nopivot);
      assert next in prev.owner;
      assert prev in flat_below;
      assert (next in flat_above) || (next == pivot);
      assert (next in fringe) || (next == pivot);
      assert t in flatten(owners_inside_nopivot);
      assert t in next.AMFO;
      assert t in flatten({next});
      if (next in fringe) { assert t in flatten(fringe); }
       else { assert next == pivot; assert t in flatten(pivot_f); }
      assert t in (flatten(fringe) + flatten(pivot_f));
    }
  }

  assert forall t <- flat_above ::(t in (flatten(fringe) + flatten(pivot_f)));

  assert ((flatten(fringe) + flatten(pivot_f)) >= flat_above);

  assert FPGE: ((flatten(fringe) + flatten(pivot.owner)) >= flat_above) by { reveal PIVOT_FO; }

  assert forall f <- flatten(fringe) :: f in flat_above;
  assert forall f <- flatten(pivot.owner) :: f in flat_above;
  assert forall f <- (flatten(fringe) + flatten(pivot.owner)) :: f in flat_above;
  SETIN((flatten(fringe) + flatten(pivot.owner)), flat_above);
  assert FPLE: (flatten(fringe) + flatten(pivot.owner)) <= flat_above;

  assert flat_above == (flatten(fringe) + flatten(pivot.owner)) by
   {
    reveal FPGE;  assert (flatten(fringe) + flatten(pivot.owner )) >= flat_above;
    reveal FPLE;  assert (flatten(fringe) + flatten(pivot.owner)) <= flat_above;
    SETLREQ((flatten(fringe) + flatten(pivot.owner)), flat_above);
   }
  assert      flat_above == (flatten(fringe) + flatten(pivot.owner));
  assert FAB: flat_above == (flatten(fringe) + flatten(pivot.owner));

  assert flat_inside_nopivot == flat_below + flat_above;
  assert flat_inside_nopivot == flat_below +  (flatten(fringe) + flatten(pivot.owner))
       by { reveal FAB;
            assert flat_above ==( (flatten(fringe) + flatten(pivot.owner)));
            assert flat_inside_nopivot == flat_below +  (flatten(fringe) + flatten(pivot.owner)); }


 assert flatten(owners_outside) == flatten(set x <- owner | outside(x, pivot));

 assert flatten(owners_inside) == flatten(owners_inside_nopivot) + pflivot(owner, pivot);
 assert flatten(owners_inside) == flat_inside_nopivot + pflivot(owner, pivot);
 assert flatten(owners_inside) == (flat_below + flat_above) + pflivot(owner, pivot);
 assert flatten(owners_inside) == (flat_below +   (flatten(fringe) + flatten(pivot.owner))  ) + pflivot(owner, pivot);

 assert BFPL: flatten(owners_inside) == (flat_below +   (flatten(fringe) + flatten(pivot.owner))  ) + pflivot(owner, pivot);

//  assert flatten(owners_inside) == ((set x <- flat_inside_nopivot | inside(x,pivot))  + (flatten(fringe) + flatten(pivot.owner))  ) + pflivot(owner, pivot);



  assert flatten(owner) == flatten(owners_outside) + flatten(owners_inside) by { reveal FLOOI; }
  assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + flatten(pivot.owner) + pflivot(owner, pivot)
    by {
         reveal FLOOI;
         assert flatten(owner) == flatten(owners_outside) + flatten(owners_inside);
         reveal BFPL;
         assert flatten(owners_inside) ==                  (flat_below + (flatten(fringe) + flatten(pivot.owner))) + pflivot(owner, pivot);
         SATAN(owner, owners_outside, owners_inside, flat_below, fringe, pivot);
         assert flatten(owner) == flatten(owners_outside) + flat_below +  flatten(fringe) + flatten(pivot.owner)   + pflivot(owner, pivot);
        }

//  assert flatten(owner) == flatten(owners_outside) + (flat_below + (flatten(fringe) + flatten(pivot.owner))) + pflivot(owner, pivot);
//  assert flatten(owner) == flatten(owners_outside) +  flat_below +  flatten(fringe) + flatten(pivot.owner)   + pflivot(owner, pivot);
//   // assert froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe) by { reveal froglet(); }
  // assert froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
  }

lemma SATAN(owner : Owner, owners_outside : Owner, owners_inside : Owner, flat_below : Owner, fringe : Owner, pivot : Object)
 requires flatten(owner) == flatten(owners_outside) + flatten(owners_inside)
 requires flatten(owners_inside) == (flat_below + (flatten(fringe) + flatten(pivot.owner))) + pflivot(owner, pivot);
  ensures flatten(owner) == flatten(owners_outside) + flat_below +  flatten(fringe) + flatten(pivot.owner)   + pflivot(owner, pivot);
{}


lemma fromTheManyOne(less : seq<nat>, more : seq<nat>)
  requires |less| == |more|
  requires forall x | 0 <= x < |less| :: less[x] <= more[x]
  ensures sum(less) <= sum(more)
{}

function sum(s : seq<int>) : int
{ if (|s| == 0) then 0 else s[0] + sum(s[1..]) }


lemma FLATTEN_OWNER(o : Object)
  requires o.Ready()
   ensures flatten(o.owner) == o.AMFX
   ensures flatten({o}) == o.AMFO  >= flatten(o.owner)
{}


lemma FLATTEN_OWNER2(o : Object, oo : Object)
  requires o.Ready()
  requires oo.Ready()
  requires oo in o.owner
   ensures flatten(o.owner) == o.AMFX
   ensures flatten({o}) == o.AMFO  >= flatten(o.owner) >= flatten({oo})
{}



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

  //       var divotInside,divotOutside,divotFringe := splitOwnersAroundPivot(divot, pivot);
  //       assert pivot in divotFringe;
  //       var divotFringeNoPivot := divotFringe - {pivot};
  //
  //       var rivetInside,rivetOutside,rivetFringe := splitOwnersAroundPivot(rivet, blivet);
  //       assert blivet in rivetFringe;
  //       var rivetFringeNoPivot := rivetFringe - {blivet};
  //
  //       assert forall o <- divotInside :: && (o in m.m.Keys);
  //       assert forall o <- divotInside :: && (klonLine(o,m.m[o],m));
  //
  //       // assert forall o <- divotInside :: && (m.m[o] in rivetInside);  //ERR GRRR
  //
  //       assert divot.AMFO   >= pivot.AMFO;
  //
  //
  //       assert forall d <- divotFringeNoPivot :: not(strictlyInside(d,pivot));
  //       assert divotFringeNoPivot <= m.m.Keys;
  //       assert forall d <- divotFringeNoPivot :: klonLine(d,m.m[d],m);
  //       assert forall d <- divotFringeNoPivot :: m.m[d] == d;




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

  assert part.AMFO   >= whole.AMFO;  //there it is????  this is it?
  assert partInside  >= wholeInside;
  assert partOutside >= wholeOutside;  //seems odd, but remember ?outside? is the upwarads closure of owners beyond the pivot.
  assert partFringe  >= wholeFringe;
}



lemma farage(ownrs : OWNR, aliens : Owner)
  //flattening anuthing within flatten(ownrs) is also in flatten(ownrs)
  requires AllReady((ownrs))
  requires AllReady((aliens))
  requires aliens <= flatten(ownrs)
  ensures forall x : Object <- flatten(ownrs) :: x.AMFO <= flatten(ownrs)
  ensures flatten(aliens) <= flatten(ownrs)
{
  var all := flatten(ownrs);
  assert isFlat(all);
  assert flatten(aliens) <= flatten(ownrs);
}


lemma farage3(ownrs : OWNR, othrs : OWNR, aliens : Owner)
 //given aliaes in flattern(ownrs), faltten(alianes) in flattern(owners
  requires AllReady((ownrs))
  requires AllReady((othrs))
  requires AllReady((aliens))
  requires othrs <= ownrs
  requires aliens <= flatten(ownrs)
  ensures forall x : Object <- flatten(ownrs) :: x.AMFO <= flatten(ownrs)
  ensures flatten(othrs)  <= flatten(ownrs)
  ensures flatten(aliens) <= flatten(ownrs)
{
  var all := flatten(ownrs);
  assert isFlat(all);

  //  assert forall o <- all, oo <- o.AMFO :: oo in all;
  //  assert forall o <- all, oo <- o.AMFO :: oo.AMFO <= all;
  //  assert forall o <- all, oo <- o.AMFO, ooo <- oo.AMFO :: oo in all;
  //  assert forall o <- all, oo <- o.AMFO, ooo <- oo.AMFO :: oo.AMFO <= all;
  //  assert forall o <- all, oo <- o.AMFO, ooo <- oo.AMFO :: ooo in all;
  //  assert forall o <- all, oo <- o.AMFO, ooo <- oo.AMFO :: ooo.AMFO <= all;

  assert forall x : Object <- all :: x.AMFO <= all;

  assert flatten(othrs)  <= flatten(ownrs);
  assert flatten(aliens) <= flatten(ownrs);

}


lemma {:timeLimit 30} makerfield(ownrs : OWNR, pivot : Object)
  requires AllReady(ownrs)   //was   requires AllReady(flatten(ownrs))
  requires pivot.Ready()
   ensures forall x <- ownrs ::    (x.AMFO >= pivot.AMFO) != (not(x.AMFO >= pivot.AMFO))
   ensures forall x <- ownrs :: not(x.AMFO >= pivot.AMFO) != not(not(x.AMFO >= pivot.AMFO))
   ensures forall x <- ownrs ::          outside(x,pivot) != not(outside(x,pivot))
   ensures forall x <- ownrs ::           inside(x,pivot) != not( inside(x,pivot))
   ensures forall x <- ownrs ::
        not(strictlyInside(x,pivot)) == (outside(x,pivot) || (x == pivot))
   ensures ownrs == (set x <- ownrs | inside(x,pivot)) + (set x <- ownrs | outside(x,pivot))
{}

lemma {:timeLimit 30} makerfield3(wholegroup : OWNR, pred : Object -> bool, ingroup : Owner, outgroup: Owner)
  requires AllReady(wholegroup)   //was   requires AllReady(flatten(wholegroup))
  requires ingroup  == set o <- wholegroup | pred(o)
  requires outgroup == set o <- wholegroup | not(pred(o))
  requires forall o <- wholegroup :: pred(o) != not(pred(o))
   ensures ingroup + outgroup == wholegroup
   ensures flatten(ingroup) + flatten(outgroup) == flatten(wholegroup)
{}


// lemma SplitAround(oo : Owner, pivot : Object) returns (sinn : Owner, sout : Owner)
//    requires AllReady(flatten(oo))
//    requires pivot.Ready()
//     ensures sinn == set o <- oo |    o.AMFO > pivot.AMFO
//     ensures sout == set o <- oo | !( o.AMFO > pivot.AMFO )
//     ensures forall o <- oo :: o in sinn || o in sout || o == pivot
//     ensures sinn !! sout !! {pivot}
//     ensures sinn+{pivot} == set o <- oo |    o.AMFO >= pivot.AMFO
//     ensures sout+{pivot} == set o <- oo |  !( o.AMFO > pivot.AMFO )
// {
//   sinn := set o <- oo |    o.AMFO > pivot.AMFO;
//   sout := set o <- oo | !( o.AMFO > pivot.AMFO );
// }



//{:timeLimit 30}
lemma {:verify false} BROKEN_insidesFlattenFringe(ownrs : OWNR, pivot : Object) returns (allInside : Owner, allOutside : Owner, fringe : Owner)
  //splits all into the bits inside pivot,
  //the bits outside pivot,
  //and the fringe (bits outside that are direct owners of an owner inside...)
  //FUCK,. shoudl this be a function?  or indeed series of functions?
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()

  requires forall o <- ownrs :: strictlyInside(o, pivot)
  requires ownrs > {}

  ensures AllReady(allInside)
  ensures AllReady(allOutside)
  ensures AllReady(fringe)

  ensures allInside  == set x <- flatten(ownrs) | strictlyInside(x, pivot)
  ensures allOutside == set x <- flatten(ownrs) | not(strictlyInside(x, pivot))
  ensures fringe == set x <- allInside, xo <- x.owner | (xo in allOutside) :: xo

  ensures allInside + flatten(fringe) == flatten(ownrs)
{
  allInside  := set x <- flatten(ownrs) | strictlyInside(x, pivot);
  allOutside := set x <- flatten(ownrs) | not(strictlyInside(x, pivot));
  fringe := set x <- allInside, xo <- x.owner | (xo in allOutside)  :: xo;

  // assert AIX: allInside  == set x <- flatten(ownrs) | strictlyInside(x, pivot);
  // assert AOX: allOutside == set x <- flatten(ownrs) | not(strictlyInside(x, pivot));
  // assert AFX: fringe == set x <- allInside, xo <- x.owner | (xo in allOutside) :: xo;

  assert allInside != {};

  assert flatten(ownrs) == allInside + allOutside;

  assert fringe <= allOutside;
  assert flatten(fringe) <= allOutside;
  FlattenContainsFlatten(ownrs,fringe);
  assert flatten(fringe) >= flatten(ownrs);
  assert flatten(fringe)  == allOutside;

  assert allInside + flatten(fringe) == flatten(ownrs);

}



function fOutside(ownrs : OWNR, pivot : Object) : (rv : Owner)
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()
  ensures AllReady(rv)
{ set x <- flatten(ownrs) | outside(x,pivot) } // not(strictlyInside(x, pivot)) }

function fInside(ownrs : OWNR, pivot : Object) : (rv : Owner)
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()
  ensures AllReady(rv)
{ set x <- flatten(ownrs) | inside(x,pivot) } //(strictlyInside(x, pivot)) }

function fStrictlyInside(ownrs : OWNR, pivot : Object) : (rv : Owner)
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()
  ensures AllReady(rv)
{ set x <- flatten(ownrs) | strictlyInside(x,pivot) } //(strictlyInside(x, pivot)) }

function fFringe(ownrs : OWNR, pivot : Object) : (rv : Owner)
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()
  ensures AllReady(rv)
{ set x <- fInside(ownrs,pivot), xo <- x.owner | (xo in fOutside(ownrs,pivot)) :: xo }


function syringe(ownrs : OWNR, pivot : Object) : (rv : Owner)
 //fringe but NOT stuff through the pivot
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()
  requires forall o <- ownrs :: inside(o,pivot)
  ensures AllReady(rv)
{ set x <- fInside(ownrs,pivot), xo <- x.owner | (x != pivot) && (xo in fOutside(ownrs,pivot)) :: xo }




function syringe_Old(ownrs : OWNR, pivot : Object) : (rv : Owner)
 //fringe but NOT stuff through the pivot
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()
  ensures AllReady(rv)
{ set x <- fStrictlyInside(ownrs,pivot), xo <- x.owner | (xo in fOutside(ownrs,pivot)) :: xo }

lemma PIVOT_OWNERS_OUTSIDE(ownrs : OWNR, pivot : Object)
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()
   ensures forall x <- pivot.owner :: outside(x,pivot)
   {}

lemma {:verify false} FLATTEN_SYRINGE(ownrs : OWNR, pivot : Object)
//anoither one that diesnt work 0- currentky not ysed
  requires ownrs > {}  //OF_COURSE_I_FJUCKING_DECREASEFUCK FUCK!!!!Q
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()
  requires forall o <- ownrs :: strictlyInside(o,pivot)  //OH How I enjoy self-hatred
//  ensures flatten(syringe(ownrs,pivot)) + flatten({pivot}) == flatten(fFringe(ownrs,pivot))
{
// assert flatten(fFringe(ownrs,pivot)) == flatten(syringe(ownrs,pivot)) + flatten({pivot}) ;
assert forall o <- ownrs :: inside(o,pivot);
assert forall o <- ownrs :: o.AMFO >= pivot.AMFO;
assert pivot in pivot.AMFO;
assert forall o <- ownrs :: pivot in o.AMFO;

assert pivot in (set o <- ownrs, oo <- o.AMFO :: oo) + ownrs;

  assert pivot in flatten(ownrs);
  assert inside(pivot, pivot);
  assert pivot in fInside(ownrs,pivot);

  var missing :=  set x <- fInside(ownrs,pivot), xo <- x.owner | (x == pivot) && (xo in fOutside(ownrs,pivot)) :: xo ;
  assert missing == set x : Object <- {pivot} , xo <- x.owner | (x == pivot) && (xo in fOutside(ownrs,pivot)) :: xo ;
  assert missing == set xo <- pivot.owner | (xo in fOutside(ownrs,pivot)) :: xo ;
  assert missing == pivot.owner;

assert pivot.AMFO == flatten(pivot.owner) + {pivot};
  assert flatten({pivot}) == flatten(pivot.owner) + {pivot};


  assert fFringe(ownrs,pivot) >= syringe(ownrs,pivot);
  assert fFringe(ownrs,pivot) == syringe(ownrs,pivot) + pivot.owner;

}


// lemma SYRINGE_STUFF(ownrs : OWNR, pivot : Object)
//   requires AllReady(flatten(ownrs))
//   requires pivot.Ready()
//    //ensures syringe(ownrs,pivot) == fFringe3((ownrs-{pivot}),ownrs,pivot)
//    {
//     //  assert (set x <- fStrictlyInside(ownrs,pivot)) == (set x <- flatten(ownrs) | strictlyInside(x,pivot));
//     //  assert (set x <- flatten(ownrs) | strictlyInside(x,pivot)) == (set x <- flatten(ownrs) | x.AMFO > pivot.AMFO);
//     //  assert (set x <- flatten(ownrs) | x.AMFO > pivot.AMFO) == (set x <- flatten(ownrs) | (x != pivot) && (x.AMFO > pivot.AMFO));
//     //  assert (set x <- flatten(ownrs) | (x != pivot) && (x.AMFO > pivot.AMFO)) == (set x <- flatten(ownrs) | (x != pivot) && (x.AMFO >= pivot.AMFO));
//     //  assert (set x <- flatten(ownrs) | (x != pivot) && (x.AMFO >= pivot.AMFO)) == (set x <- flatten(ownrs-{pivot}) | (x != pivot) && (x.AMFO >= pivot.AMFO));
//     //  assert (set x <- flatten(ownrs) | (x != pivot) && (x.AMFO >= pivot.AMFO)) == (set x <- flatten(ownrs-{pivot}) | (x != pivot) && (x.AMFO >= pivot.AMFO));
//
//      assert (set x <- fStrictlyInside(ownrs,pivot)) == (set x <- flatten(ownrs) | strictlyInside(x,pivot));
//      assert (set x <- fStrictlyInside(ownrs,pivot)) == (set x <- flatten(ownrs) | x.AMFO > pivot.AMFO);
//      assert (set x <- fStrictlyInside(ownrs,pivot)) == (set x <- flatten(ownrs) | (x != pivot) && (x.AMFO > pivot.AMFO));
//      assert (set x <- fStrictlyInside(ownrs,pivot)) == (set x <- flatten(ownrs) | (x != pivot) && (x.AMFO >= pivot.AMFO));
//      assert (set x <- flatten(ownrs) | (x != pivot) && (x.AMFO >= pivot.AMFO))
//                                                     == (set x <- flatten(ownrs-{pivot}) | (x != pivot) && (x.AMFO >= pivot.AMFO));
//      assert not( strictlyInside(pivot,pivot) );
//      FLATTEN_SUBS(ownrs,{pivot});
//      assert flatten(ownrs) == flatten(ownrs-{pivot}) + flatten({pivot});
//
//     //  assert (set x <- flatten(ownrs-{pivot}) | (x != pivot) && (x.AMFO >= pivot.AMFO))
//     //      == (set x <- flatten(ownrs-{pivot}) |                 (x.AMFO >= pivot.AMFO));
//    }

function fFringe3(iwnrs : OWNR,  ownrs : OWNR, pivot : Object) : (rv : Owner)
  requires AllReady(flatten(iwnrs))
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()
   ensures AllReady(rv)
{ set x <- fInside(iwnrs,pivot), xo <- x.owner | (xo in fOutside(ownrs,pivot)) :: xo }



lemma INSIDE_OUTSIDE(ownrs : OWNR, pivot : Object)
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()
  ensures flatten(ownrs) == (fInside(ownrs,pivot) + fOutside(ownrs,pivot))
{}
//    opaque {
//         assert all == (allInside + allOutside);
//         assert forall x <- allOutside :: not(strictlyInside(x, pivot));
//         assert allOutside == all - allInside;
//         assert pivot in allOutside;
//
//         assert forall x : Object <- all :: x.AMFO <= all;
//         assert forall x <- allInside :: x.AMFO <= all;
//         assert forall x <- allOutside :: x.AMFO <= all;
//
//         assert forall x <- all :: strictlyInside(x, pivot) != not(strictlyInside(x, pivot));
//         assert allInside !! allOutside;
//
//         assert fringe <= allOutside;
//
//    }


opaque predicate froglet(owner : Owner, pivot : Object, owners_inside : Owner, owners_outside : Owner, flat_below : Owner, fringe : Owner)
   //yep, ownerinside is ignored!
   //call as froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe)
  { flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot) }
//  { flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + flatten({pivot}) }

function nu_pflivot(owner : Owner, pivot : Object) : (fp : OWNR)
  { if (exists x <- owner :: inside(x, pivot))
      then flatten(pivot.owner) else {} }

lemma nu_PFLIVOT_IS_FLATTEN_PIVOT_0(owner : Owner, pivot : Object)
  requires exists x <- owner :: inside(x, pivot)
   ensures nu_pflivot(owner,pivot) ==  flatten(pivot.owner)
   {}

//weird pivot
function pflivot(owner : Owner, pivot : Object) : (fp : OWNR)
  { if (pivot in owner) then flatten({pivot}) else {} }

function correct_pflivot(owner : Owner, pivot : Object) : (fp : OWNR)
  { if (exists x <- owner :: inside(x, pivot))
      then flatten({pivot}) else {} }

lemma PFLIVOT_IS_FLATTEN_PIVOT_0(owner : Owner, pivot : Object)
  requires exists x <- owner :: inside(x, pivot)
   ensures pflivot(owner,pivot) ==  flatten({pivot})
   {}

lemma NU_PFLIVOT_IS_FLATTEN_PIVOT_1(owner : Owner, pivot : Object)
  requires pivot.Ready()
  requires exists x <- owner :: inside(x, pivot)
   ensures flatten({pivot}) == {pivot} + flatten(pivot.owner)
   ensures pflivot(owner,pivot) ==  flatten({pivot})
   ensures nu_pflivot(owner,pivot)  + {pivot} ==  flatten({pivot})
   {}


lemma {:verify false} X_DaysOfOpenHand(left : Owner, la : Owner, lb : Owner, lc : Owner, right : Owner, ra : Owner, rb : Owner, rc : Owner)
  requires AllReady(flatten(left))
  requires AllReady(flatten(right))
  requires flatten(la) !! flatten(lb) !! flatten(lc)
  requires flatten(ra) !! flatten(rb) !! flatten(rc)
  requires left  == la + lb + lc
  requires right == ra + rb + rc
  {
    // assert left  == la + lb + lc;
    // assert right == ra + rb + rc;

    // assert (left >= right)  ==> ((la >= ra) && (lb >= rb) && (lc >= rc));
    // assert (left >= right) <==  ((la >= ra) && (lb >= rb) && (lc >= rc));



    assert (flatten(left) >= flatten(right))  ==> ((flatten(la) >= flatten(ra)) && (flatten(lb) >= flatten(rb)) && (flatten(lc) >= flatten(rc)));
    assert (flatten(left) >= flatten(right)) <==  ((flatten(la) >= flatten(ra)) && (flatten(lb) >= flatten(rb)) && (flatten(lc) >= flatten(rc)));

  }

lemma flatten_monotonic(a : Owner, b : Owner)
  // requires AllReady(a)
  // requires AllReady(b)
   ensures (a == b) ==> flatten(a) == flatten(b)
   ensures (a < b) ==> flatten(a) <= flatten(b)
   ensures (a > b) ==> flatten(a) >= flatten(b)
{}

lemma  NAKED_LIBERATION(li : Owner, lo : Owner, lb : Owner, lf : Owner,
                 ri : Owner, ro : Owner, rb : Owner, rf : Owner,
                 left : Owner, right : Owner, pivot : Object)
                    requires left  == (li + lo + lb + lf + pflivot(left, pivot) )
                    requires right == (ri + ro + rb + rf + pflivot(right,pivot) )
  requires ((li) >= (ri))
  requires ((lo) >= (ro))
  requires (lb >= rb)
  requires ((lf) >= (rf))
  requires (pflivot(left, pivot) >= pflivot(right,pivot))
   ensures ((left) >= (right))
{}


lemma  FLAT_LIVERATUIB(li : Owner, lo : Owner, lb : Owner, lf : Owner,
                 ri : Owner, ro : Owner, rb : Owner, rf : Owner,
                 left : Owner, right : Owner, pivot : Object)
                    requires froglet(left, pivot,li,lo,lb,lf)
                    requires froglet(right,pivot,ri,ro,rb,rf)

  requires ((li) >= (ri))
  requires ((lo) >= (ro))
  requires (lb >= rb)
  requires ((lf) >= (rf))
  requires (pflivot(left, pivot) >= pflivot(right,pivot))
   ensures (flatten(left) >= (right))
{
  reveal froglet();
  flatten_monotonic(li,ri);
  flatten_monotonic(lo,ro);
  flatten_monotonic(lb,rb);
  flatten_monotonic(lf,rf);
  flatten_monotonic(pflivot(left, pivot),pflivot(right, pivot));


  assert flatten(li) >= flatten(ri);
  assert flatten(lo) >= flatten(ro);
  assert flatten(lb) >= flatten(rb);
  assert flatten(lf) >= flatten(rf);
  assert (pflivot(left, pivot) >= pflivot(right,pivot));

  assert flatten(left)  == flatten(lo) + lb + flatten(lf) + pflivot(left,  pivot);
  assert flatten(right) == flatten(ro) + rb + flatten(rf) + pflivot(right, pivot);

   assert ((flatten(lo) >= flatten(ro)) && (lb >= rb) && (flatten(lf) >= flatten(rf)) && (pflivot(left, pivot) >= pflivot(right,pivot)) );
}


lemma DaysOfOpenHand2(left : Owner, right : Owner, pivot : Object)
///this is totally brokwn.
///BUT see "FLAT_LIVERATUIB" above. that shows things will all work, doesn't it?
///
        //  li : Owner, lo : Owner, lb : Owner, lf : Owner,
        //  ri : Owner, ro : Owner, rb : Owner, rf : Owner)

  requires AllReady(flatten(left))
  requires AllReady(flatten(right))
  requires pivot.Ready()
  // requires flatten(left) >= pivot.AMFO
  // requires flatten(right) >= pivot.AMFO
  requires exists x <- left :: inside(x, pivot) ///hmmmm
  requires exists x <- right :: inside(x, pivot) ///hmmmm

  // ensures (flatten(left) >= flatten(right)) <== ((flatten(lo) >= flatten(ro)) && (lb >= rb) && (flatten(lf) >= flatten(rf)))

  // requires (flatten(lo) >= flatten(ro))
  // requires (lb >= rb)
  // requires (flatten(lf) >= flatten(rf))
  // requires (pflivot(left, pivot) >= pflivot(right,pivot))

  //  ensures (flatten(left) >= flatten(right))
{
  var li,lo,lb,lf := tiredOfSleeping(left, pivot);
  var ri,ro,rb,rf := tiredOfSleeping(right, pivot);

  assert flatten(left)  == flatten(lo) + lb + flatten(lf) + pflivot(left,  pivot);
  assert flatten(right) == flatten(ro) + rb + flatten(rf) + pflivot(right, pivot);

  assert li !! lo;
  assert flatten(li) >= lb;
  assert flatten(left) == flatten(li) + flatten(lo);    //flatten is monotinic

  assert (flatten(left) >= flatten(right)) <== ((flatten(lo) >= flatten(ro)) && (lb >= rb) && (flatten(lf) >= flatten(rf)) && (pflivot(left, pivot) >= pflivot(right,pivot)) );
  assert (flatten(left) >= flatten(right)) ==> ((flatten(lo) >= flatten(ro)) || (lb >= rb) || (flatten(lf) >= flatten(rf)) || (pflivot(left, pivot) >= pflivot(right,pivot)) );


  assert (flatten(lo) >= flatten(ro));
  assert (lb >= rb);
  assert (flatten(lf) >= flatten(rf));
  assert (pflivot(left, pivot) >= pflivot(right,pivot));

  assert (flatten(left) >= flatten(right));
}

//{:timeLimit 30}
lemma {:timeLimit 60}
tiredOfSleeping(owner : Owner, pivot : Object)
  returns (owners_inside : Owner, owners_outside : Owner, flat_below : Owner, fringe : Owner)
  //FUCK,. shoudl xGG indeed series of functions?
  //pivot or Klon??
//likely needs at least 20s to verify on M2
 requires AllReady(flatten(owner))
 requires pivot.Ready()     requires piR: pivot.Ready()
//requires flatten(owner) >= pivot.AMFO

// requires exists x <- owner :: inside(x, pivot) ///hmmmm

  ensures owners_inside ==  set x <- owner |  inside(x, pivot)
  ensures owners_outside == set x <- owner | outside(x, pivot)
  ensures owner == owners_outside + owners_inside
  ensures flatten(owner) == flatten(owners_inside) + flatten(owners_outside)

  ensures flat_below == set x <- flatten(owners_inside) | inside(x,pivot)
  ensures fringe == set x <- flatten(owners_inside), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo

  ensures reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe)
  ensures flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot)

  ensures owners_inside <= flat_below
  ensures flat_below <= flatten(owners_inside)

{
  owners_inside, owners_outside := SplitTheDeadOwners(owner, pivot);

  if (owners_inside == {})
  {
    flat_below := {}; fringe := {};
    assert owners_outside == owner;
    // assert flat_below == {};
    assert flatten(owner) == flatten(owners_outside);
    // assert flatten(fringe) == {};

    assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot);
    assert reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);

    return;
    //a more dedicated model could do more here, but not needed for correctness
  }

  if (owners_inside == {pivot})
  {
    flat_below := {pivot}; fringe := {};
    assert owners_outside == owner - {pivot};
    assert flat_below == {pivot};
    assert flatten(fringe) == {};
    assert flatten(owner) == flatten(owners_outside) + {pivot} + {} + pflivot(owner, pivot);


    assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot);
    assert reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);

    return;
    //a more dedicated model could do more here, but not needed for correctness
  }
 flat_below := {pivot}; fringe := {};
  return;

  assert owners_inside > {};

  assert pflivot(owner, pivot) == flatten({pivot});

  flat_below := set x <- flatten(owners_inside) | inside(x,pivot);   ///pivot will be inside
  var flat_above := set x <- flatten(owners_inside) | outside(x,pivot);
  assert flatten(owners_inside) == flat_below + flat_above;

var flatI,flatO,fw := FlattenFringeIsAllOutside(owners_inside - {pivot},pivot);
assert flatten(fw) <= flatO;

assert flatI == flat_below;
assert flatO == flat_above;

var whole_f;
var pivot_f;

whole_f,fringe,pivot_f := GordonRamseyThemFringes(owners_inside, pivot);

// //////////////////////////////////////////////////////////////////////////////////////////////////////////
// assume flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot);
//   assert reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
//       return;
//////////////////////////////////////////////////////////////////////////////////////////////////////////


assert   fringe   == set x  <- flatten(owners_inside), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
assert   whole_f  == set x  <- flatten(owners_inside), xo <- x.owner |                  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
assert   pivot_f  == set x  <- flatten(owners_inside), xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;

//jun4 assert fw == whole_f;
//jun4 assert flatten(whole_f) == flat_above;


//
// assert fw == whole_f;
// assert flatten(whole_f) == flat_above;
//
// assert (set x  <- flatten(owners_inside), xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo)
//           ==
//        (set x : Object <- {pivot}, xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo);
//
// assert (set x : Object <- {pivot}, xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo)
//           ==
//        (set xo <- pivot.owner | (inside(pivot,pivot) ) && (outside(xo,pivot) ) :: xo);
//
// assert forall xo <- pivot.owner :: (inside(pivot,pivot) ) && (outside(xo,pivot));
//
// assert (set xo <- pivot.owner | (inside(pivot,pivot) ) && (outside(xo,pivot) ) :: xo)
//           ==
//        (set xo <- pivot.owner :: xo)
//           ==
//        (pivot.owner);
//
//
//  assert pivot_f == pvtfrng == pivot.owner;
//
// forall x <- flatten(owners_inside), xo <- x.owner ensures (whole_f == pivot_f + fringe) {
//  if ( (inside(x,pivot) ) && (outside(xo,pivot) ) )
//    {
//     assert xo in whole_f;
//     if (x == pivot)
//       {
//          assert xo in pivot_f;
//          assert xo in pvtfrng;
//          assert xo in pivot.owner;
//          assert pivot_f == pvtfrng == pivot.owner;
//       } else {
//          assert xo in fringe;
//          //assert pivot_f == pvtfrng;
//       }
//       assert (xo in pivot_f) || (xo in fringe);
//       assert whole_f == pivot_f + fringe;
//     //  assert pivot_f == pvtfrng == pivot.owner;
//
//    } //end if
//
//
// }//end foreach
//
//   assert whole_f == fringe + pivot_f;
//   assert whole_f == fringe + pivot.owner;

//jun04  assert flatten(whole_f) == flat_above;
//jun04   assert flatten(fringe + pivot.owner) == flat_above;
//jun04   assert flatten(fringe) + flatten(pivot.owner) == flat_above;
//jun04
//jun04   assert flat_above == flatten(fringe + pivot.owner);
//jun04   assert flat_above == flatten(fringe) + flatten(pivot.owner);
//jun04
//jun04   assert flatten({pivot}) == {pivot} + flatten(pivot.owner);
//jun04   assert flat_above == flatten(fringe) + flatten(pivot.owner);
//jun04   assert flat_above + {pivot} == flatten(fringe) + flatten({pivot});
//jun04
//jun04   assert pivot in flat_below;
//jun04   assert flat_below + flat_above == flat_below + flatten(fringe) + flatten({pivot});


  assert flatten(owners_inside) == flat_below + flat_above;
  assert flatten(owners_inside) == flat_below + flatten(fringe) + flatten({pivot});

  assert flatten(owner) == flatten(owners_outside) + flatten(owners_inside);
  assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + flatten({pivot});
  assert froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe) by { reveal froglet(); }
  assert froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
}



datatype Segmented = Segmented(owner : Owner,  rat : nat)


//{:timeLimit 30}   {:timeLimit 60} {:timeLimit 120}
lemma {:verify false} X_shouldBeSleeping(ownrs : OWNR, pivot : Object) returns (onnsiders : Owner, offsiders : Owner, allInside : Owner, allOutside : Owner, fringe : Owner)
  //REPLACED by tiredOfSleeping
  //splits all into the bits inside pivot,
  //the bits outside pivot,
  //and the fringe (bits outside that are direct owners of an owner inside...)
  //FUCK,. shoudl this be a function?  or indeed series of functions?
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()     requires piR: pivot.Ready()


///MISTAKE??   requires ownrs > pivot.AMFO  //the catch here is that it is possible x in ownrs but not(inside(x,pivot))
  //say8ng exists x : strictlyInside(x,pivot) is anaother option...
  //also; making oaners > pivot,AMFO is on reflection, clearly WRONG.,

  ensures AllReady(allInside)
  ensures AllReady(allOutside)
  ensures AllReady(fringe)


  //  ensures allOutside == set x <- flatten(ownrs) | not(strictlyInside(x, pivot))
  //  ensures allInside !! allOutside
  //  ensures flatten(ownrs) == (allInside + allOutside)
  //  ensures fringe == set x <- allInside, xo <- x.owner | (xo in allOutside)  :: xo
  //  ensures fringe <= allOutside

  //    ensures (allInside > {}) ==> (flatten(fringe) == allOutside)    //ERR
  //    ensures (allInside > {}) ==> (pivot in fringe)
  //
  //    ensures (fringe - {pivot}) == set x <- allInside, xo <- x.owner | (xo in allOutside) && (xo != pivot) :: xo    //ERR
  //    ensures flatten(fringe - {pivot}) + flatten({pivot}) == flatten(fringe) == allOutside                        //ERR

{
  onnsiders, offsiders := SplitTheDeadOwners(ownrs, pivot);

  if (onnsiders == {})
  {
    allInside := {};  allOutside := flatten(ownrs); fringe := {}; return;
    //a more dedicated model could do more here, but not needed for correctness
  }

  assert onnsiders > {};

  assert SONN: onnsiders == set x <- ownrs |  inside(x, pivot);
  assert SOFF: offsiders == set x <- ownrs | outside(x, pivot);
  assert SUMM: ownrs == offsiders + onnsiders;

 // assert pivot in onnsiders;

  var flatOnnsiders := flatten(onnsiders);
  allInside  := fInside(onnsiders,pivot);
  allOutside := fOutside(onnsiders,pivot);
  fringe := fFringe(onnsiders,pivot);


  INSIDE_OUTSIDE(onnsiders, pivot);

  // var probe :| probe in fInside(onnsiders,pivot);
//   // PivotInFringe(ownrs, pivot, probe);
//
//   farage(onnsiders, {probe});
//   assert probe.AMFO <= flatOnnsiders;
//   farage(onnsiders, allOutside);
//   assert flatten(allOutside) <= flatOnnsiders;

assert pivot  in allInside;
assert pivot !in fringe;
assert pivot !in flatten(fringe);
//
//   var fringeNoPivot:= fringe - {pivot};
//   assert pivot !in fringeNoPivot;
//   var flatFringeNoPivot := flatten(fringeNoPivot);
//
//   Notin(onnsiders, pivot, allInside, allOutside, fringe);
//   assert pivot !in flatten(fringe - {pivot});
//   assert pivot !in flatFringeNoPivot;
//   FLATTEN_SUBS(fringe, {pivot});
//   assert flatten(fringe - {pivot}) + flatten({pivot}) == flatten(fringe);// == allOutside;

//  assert flatten(fringe) + pivot.AMFO == allOutside;

  // assert allOutside == set x <- flatten(ownrs) | not(strictlyInside(x, pivot)) by { reveal AOX; }
  // assert allInside  == set x <- flatten(ownrs) | strictlyInside(x, pivot) by { reveal AIX; }
  // assert fringe == set x <- allInside, xo <- x.owner | (xo in allOutside) :: xo  by { reveal AFX; }
  // assert  (allInside > {}) ==> (flatten(fringe) == allOutside);

  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //




///GOLLUM assert forall x <- ownrs :: (x.AMFO >= pivot.AMFO) != not(x.AMFO >= pivot.AMFO); //ERR
///GOLLUM assert forall x <- ownrs :: (outside(x, pivot) != not(outside(x, pivot)));       //ERR

  //
  // assert ownrs == offsiders + onnsiders;   //WZAEMMES
  // assert flatten(ownrs) == (flatten(offsiders) + flatten(onnsiders));              //ERR
  // assert offsiders !! onnsiders;
  //









assert forall o <- offsiders :: o in fOutside(ownrs,pivot);
assert forall o <- offsiders :: o.AMFO <= flatten(offsiders);
assert allInside <= flatten(onnsiders) <= flatOnnsiders;

assert fInside(offsiders, pivot) ==  {};
assert fFringe(offsiders, pivot) ==  {};
assert fInside(onnsiders+offsiders, pivot) ==  fInside(onnsiders,pivot);
assert (onnsiders+offsiders) == ownrs by { reveal SUMM; }
assert fInside(ownrs, pivot) == fInside(onnsiders, pivot);

assert (set x <- fInside(ownrs,pivot), xo <- x.owner | (xo in fOutside(ownrs,pivot)) :: xo)
          == fFringe3(ownrs, ownrs, pivot)
          == fFringe(ownrs, pivot);

//assert fFringe3(ownrs, ownrs, pivot) == fInside(ownrs, pivot);
assert fFringe3(ownrs, ownrs, pivot)     == fFringe3(onnsiders, ownrs, pivot);
///assert fFringe3(onnsiders, ownrs, pivot) >= fFringe3(onnsiders, onnsiders, pivot);

//KJX May25 2026 - this code about fringes ins unfinished (and perhaps unnecessary)

// assert fFringe(ownrs, pivot) == fFringe(onnsiders, pivot);


// opaque { assert fringe == set x <- fInside(ownrs,pivot), xo <- x.owner     | (xo in fOutside(onnsiders,pivot)) :: xo; }
// opaque {  assert fringe == set x <- fInside(ownrs,pivot), xo <- x.owner     | (xo in fOutside(ownrs,pivot)) :: xo; }
// opaque {  assert fringe == set x <- fInside(onnsiders,pivot), xo <- x.owner | (xo in fOutside(ownrs,pivot)) :: xo; }
// opaque {  assert fringe == set x <- fInside(onnsiders,pivot), xo <- x.owner | (xo in fOutside(onnsiders,pivot)) :: xo; }


  assert flatten(ownrs) == flatten(onnsiders) + flatten(offsiders) by
   {  reveal SONN, SOFF, SUMM;
      assert onnsiders + offsiders == ownrs;
    FLATTEN_SUM3(onnsiders,offsiders,ownrs); }    //but not necessarily disjoint

  assert fInside(ownrs, pivot) == fInside(onnsiders, pivot) + fInside(offsiders, pivot);

forall f <- offsiders ensures (forall x <- f.AMFO :: outside(x,pivot)) {
        FlattenOutsideFlatten(f,pivot);
}




  assert forall x <- fInside(ownrs,pivot), xo <- x.owner  :: xo in flatten(ownrs);

//   assert fFringe(ownrs, pivot) == fFringe(onnsiders, pivot); //but its not but it doesn't matter.


 var onnInside, onnOutside, onnFringe := FlattenFringeIsAllOutside(onnsiders, pivot);
 assert onnInside == allInside;
 assert onnOutside == allOutside;
 assert onnFringe == fringe;

assert flatten(onnsiders) == allInside + allOutside;

assert flatten(fringe) == allOutside;   ///THHIS ONE!!!



assert allInside + flatten(fringe) == flatten(onnsiders);
assert flatten(onnsiders) + flatten(offsiders) == flatten(ownrs);


INSIDE_OUTSIDE(ownrs,pivot);
assert flatten(ownrs) == fInside(ownrs,pivot) +  fOutside(ownrs,pivot);

assert flatten(ownrs) == fInside(onnsiders,pivot) +  fOutside(ownrs,pivot);

///ERR assert fOutside(ownrs,pivot) == flatten(fFringe(ownrs,pivot)) + flatten(offsiders);

//lassert fOutside(ownrs,pivot) == flatten(fFringe(ownrs,pivot)) + flatten(offsiders);

assert pivot in allInside;

 var fringeNoPivot := fringe - {pivot};
// FLATTEN_SUBS(fringe,{pivot});

// assert fFringe({pivot},pivot) == {};
// assert fFringe(ownrs,pivot) == fFringe(ownrsNoPivot,pivot) + fFringe({pivot},pivot);
// assert fFringe(ownrs,pivot) == fFringe(ownrsNoPivot,pivot) + {pivot};

assert flatten(fFringe(ownrs,pivot)) == flatten(fringeNoPivot) + flatten({pivot});

assert flatten(ownrs) == fInside(onnsiders,pivot) + flatten(fFringe(ownrs,pivot)) + flatten(offsiders);


}




//{:timeLimit 30}   {:timeLimit 60} {:timeLimit 120}
lemma {:verify false} XsplitOWNRSroundPivot(ownrs : OWNR, pivot : Object) returns (allInside : Owner, allOutside : Owner, fringe : Owner)
  //splits all into the bits inside pivot,
  //REPLACED by tiredOfSleeping
  //the bits outside pivot,
  //and the fringe (bits outside that are direct owners of an owner inside...)
  //FUCK,. shoudl this be a function?  or indeed series of functions?
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()     requires piR: pivot.Ready()


///MISTAKE??   requires ownrs > pivot.AMFO  //the catch here is that it is possible x in ownrs but not(inside(x,pivot))
  //say8ng exists x : strictlyInside(x,pivot) is anaother option...
  //also; making oaners > pivot,AMFO is on reflection, clearly WRONG.,

  ensures AllReady(allInside)
  ensures AllReady(allOutside)
  ensures AllReady(fringe)

  //  ensures allOutside == set x <- flatten(ownrs) | not(strictlyInside(x, pivot))
  //  ensures allInside !! allOutside
  //  ensures flatten(ownrs) == (allInside + allOutside)
  //  ensures fringe == set x <- allInside, xo <- x.owner | (xo in allOutside)  :: xo
  //  ensures fringe <= allOutside




  //    ensures (allInside > {}) ==> (flatten(fringe) == allOutside)    //ERR
  //    ensures (allInside > {}) ==> (pivot in fringe)
  //
  //    ensures (fringe - {pivot}) == set x <- allInside, xo <- x.owner | (xo in allOutside) && (xo != pivot) :: xo    //ERR
  //    ensures flatten(fringe - {pivot}) + flatten({pivot}) == flatten(fringe) == allOutside                        //ERR

{
  if (forall o <- ownrs :: not(strictlyInside(o, pivot)))
  {
    allInside := {};  allOutside := flatten(ownrs); fringe := {}; return;
    //a more dedicated model could do more here, but not needed for correctness
  }

  var all := flatten(ownrs);
  allInside  := fInside(ownrs,pivot);
  allOutside := fOutside(ownrs,pivot);
  fringe := fFringe(ownrs,pivot);

  INSIDE_OUTSIDE(ownrs, pivot);



  //   assert exists x <- allInside :: (x.AMFO > pivot.AMFO) && (x.Ready());   //cos we know theere is something in AllInside or we'd have quit.

  var probe :|  probe in  fInside(ownrs,pivot);
  // assert (probe.AMFO > pivot.AMFO);
  // assert (probe in allInside);

  XPivotInFringe(ownrs, pivot, probe);

  farage(ownrs, {probe});
  assert probe.AMFO <= all;


  farage(ownrs, allOutside);
  assert flatten(allOutside) <= all;


  //
  // // assert forall t <- allOutside :: t.AM551t                                           ot(strictlyInside(t, pivot));
  //     ///THIS IS WRONG WERONG WONGO WRONG assert forall t <- allOutside, i <- allInside :: strictlyInside(i,t);
  //
  // assert  forall t <- allOutside, i <- allInside ::  strictlyInside(i,t) ==> t in i.AMFO;
  // assert  forall t <- allOutside, i <- allInside ::  inside(i,t) ==> t in i.AMFO;
  // assert  forall t <- allOutside, i <- allInside ::  inside(i,t) ==> t in flatten({i});
  //
  // // assert  forall t <- all        :: exists  o <- ownrs :: inside(t,o);
  // // assert  forall t <- all        :: exists  o <- ownrs :: t in flatten({o});
  // // assert forall t <- all  ::  flatten(ownrs)
  //
  // assert  forall t <- all        :: exists  o <- ownrs :: t in o.AMFO;
  // assert  forall t <- allInside  :: exists  o <- ownrs :: t in o.AMFO;
  // assert  forall t <- allOutside :: exists  o <- ownrs :: t in o.AMFO;
  //
  // //????assert  forall t <- allOutside, o <- ownrs :: strictlyInside(o,pivot) && t in flatten({o});
  // //
  // //
  // //   forall t <- allOutside, i <- allInside
  // //      |  strictlyInside(i,t) //&& strictlyInside(i,pivot) // && not(strictlyInside(t, pivot))
  // //       ensures (t in flatten(fringe))
  // //   {
  // //       var prev, next := AcrossTheBorder(i, pivot, t); //TODO TODO TODO
  // //       assert strictlyInside(prev,t);
  // //       assert not(strictlyInside(next,pivot));
  // //       assert prev in all;
  // //       assert next in prev.owner;
  // //       assert prev in allInside;
  // //       assert next in allOutside;
  // //       assert next in fringe;
  // //       assert t in all;
  // //       assert t in next.AMFO;
  // //       assert t in flatten({next});
  // //   }
  // //

  var fringeNoPivot:= fringe - {pivot};
  assert pivot !in fringeNoPivot;

  var flatFringeNoPivot := flatten(fringeNoPivot);

  Notin(ownrs, pivot, allInside, allOutside, fringe);

  //////////////////////////////////////////////////////////////////////////////

  assert pivot !in flatten(fringe - {pivot});
  assert pivot !in flatFringeNoPivot; //ERR





  // assert fringe == set x <- allInside, xo <- x.owner | (xo in allOutside) :: xo  by { reveal AFX; }
  //   assert fringeNoPivot == set x <- allInside, xo <- x.owner | (xo in allOutside) && (xo != pivot) :: xo;
  //  //ERR
  //   assert (fringe - {pivot}) == set x <- allInside, xo <- x.owner | (xo in allOutside) && (xo != pivot) :: xo;

  FLATTEN_SUBS(fringe, {pivot});
  assert flatten(fringe - {pivot}) + flatten({pivot}) == flatten(fringe); // == allOutside;

  // assert allOutside == set x <- flatten(ownrs) | not(strictlyInside(x, pivot)) by { reveal AOX; }
  // assert allInside  == set x <- flatten(ownrs) | strictlyInside(x, pivot) by { reveal AIX; }
  // assert fringe == set x <- allInside, xo <- x.owner | (xo in allOutside) :: xo  by { reveal AFX; }
  // assert  (allInside > {}) ==> (flatten(fringe) == allOutside);

  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

  var onnsiders, offsiders := SplitTheDeadOwners(ownrs, pivot);

  assert sonn: onnsiders == set x <- ownrs |  inside(x, pivot);
  assert soff: offsiders == set x <- ownrs | outside(x, pivot);
  assert summ: ownrs == offsiders + onnsiders;


  // makerfield(ownrs, pivot);

///GOLLUM assert forall x <- ownrs :: (x.AMFO >= pivot.AMFO) != not(x.AMFO >= pivot.AMFO); //ERR
///GOLLUM assert forall x <- ownrs :: (outside(x, pivot) != not(outside(x, pivot)));       //ERR

  //
  // assert ownrs == offsiders + onnsiders;   //WZAEMMES
  // assert flatten(ownrs) == (flatten(offsiders) + flatten(onnsiders));              //ERR
  // assert offsiders !! onnsiders;
  //









assert forall o <- offsiders :: o in allOutside;
assert forall o : Object <- offsiders :: o.AMFO <= allOutside;
assert flatten(offsiders) <= allOutside;
assert allInside <= flatten(onnsiders) <= all;

assert forall f <- offsiders, x <- f.AMFO :: x in allOutside;
assert fInside(offsiders, pivot) ==  {};
assert fFringe(offsiders, pivot) ==  {};
assert fInside(onnsiders+offsiders, pivot) ==  fInside(onnsiders,pivot);
assert (onnsiders+offsiders) == ownrs by { reveal summ; }
assert fInside(ownrs, pivot) == fInside(onnsiders, pivot);

assert (set x <- fInside(ownrs,pivot), xo <- x.owner | (xo in fOutside(ownrs,pivot)) :: xo)
          == fFringe3(ownrs, ownrs, pivot)
          == fFringe(ownrs, pivot);

//assert fFringe3(ownrs, ownrs, pivot) == fInside(ownrs, pivot);
assert fFringe3(ownrs, ownrs, pivot)     == fFringe3(onnsiders, ownrs, pivot);
///assert fFringe3(onnsiders, ownrs, pivot) >= fFringe3(onnsiders, onnsiders, pivot);

// assert fFringe(ownrs, pivot) == fFringe(onnsiders, pivot);


// opaque { assert fringe == set x <- fInside(ownrs,pivot), xo <- x.owner     | (xo in fOutside(onnsiders,pivot)) :: xo; }
// opaque {  assert fringe == set x <- fInside(ownrs,pivot), xo <- x.owner     | (xo in fOutside(ownrs,pivot)) :: xo; }
// opaque {  assert fringe == set x <- fInside(onnsiders,pivot), xo <- x.owner | (xo in fOutside(ownrs,pivot)) :: xo; }
// opaque {  assert fringe == set x <- fInside(onnsiders,pivot), xo <- x.owner | (xo in fOutside(onnsiders,pivot)) :: xo; }


  assert flatten(ownrs) == flatten(onnsiders) + flatten(offsiders) by
   {  reveal sonn, soff, summ;
      assert onnsiders + offsiders == ownrs;
    FLATTEN_SUM3(onnsiders,offsiders,ownrs); }    //but not necessarily disjoint

  assert fInside(ownrs, pivot) == fInside(onnsiders, pivot) + fInside(offsiders, pivot);
  assert fFringe(ownrs, pivot) == fFringe(onnsiders, pivot) + fFringe(offsiders, pivot);


forall f <- offsiders ensures (forall x <- f.AMFO :: outside(x,pivot)) {
        FlattenOutsideFlatten(f,pivot);
}




  assert forall x <- fInside(ownrs,pivot), xo <- x.owner  :: xo in flatten(ownrs);

//   assert fFringe(ownrs, pivot) == fFringe(onnsiders, pivot);


 var onnInside, onnOutside, onnFringe := FlattenFringeIsAllOutside(onnsiders, pivot);

assert allInside + flatten(fringe) == flatten(onnsiders);
assert flatten(onnsiders) + flatten(offsiders) == flatten(ownrs);



assert flatten(ownrs) == allInside + allOutside;

assert flatten(ownrs) == fInside(ownrs,pivot) +  fOutside(ownrs,pivot);
assert flatten(ownrs) == fInside(onnsiders,pivot) +  fOutside(ownrs,pivot);
assert flatten(ownrs) == fInside(onnsiders,pivot) +  fOutside(ownrs,pivot);

//lassert fOutside(ownrs,pivot) == flatten(fFringe(ownrs,pivot)) + flatten(offsiders);
assert flatten(ownrs) == fInside(onnsiders,pivot) + flatten(fFringe(ownrs,pivot)) + flatten(offsiders);


  assert allOutside == set x <- flatten(ownrs) | not(strictlyInside(x, pivot));
  assert allInside == set x <- flatten(ownrs) | strictlyInside(x, pivot);
  assert fringe == set x <- allInside, xo <- x.owner | (xo in allOutside) :: xo;
}




lemma SplitTheDeadOwners(ownrs : OWNR, pivot : Object) returns (onnsiders : Owner, offsiders : Owner)
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()
  ensures onnsiders == set x <- ownrs |  inside(x, pivot)
  ensures offsiders == set x <- ownrs | outside(x, pivot)
  ensures ownrs == offsiders + onnsiders
  ensures ownrs - offsiders == onnsiders
  ensures ownrs - onnsiders == offsiders
  ensures offsiders !! onnsiders
  ensures flatten(ownrs) == (flatten(offsiders) + flatten(onnsiders))
  ensures flatten(ownrs) >=  flatten(offsiders)
  ensures flatten(ownrs) >=  flatten(onnsiders)
{
  onnsiders := set x <- ownrs |  inside(x, pivot);
  offsiders := set x <- ownrs | outside(x, pivot);  //outside df not inside.

  makerfield(ownrs, pivot);

///GOLLUM assert forall x <- ownrs :: (x.AMFO >= pivot.AMFO) != not(x.AMFO >= pivot.AMFO); //ERR
///GOLLUM assert forall x <- ownrs :: (outside(x, pivot) != not(outside(x, pivot)));       //ERR

  assert ownrs == offsiders + onnsiders;
  assert offsiders !! onnsiders;
  assert flatten(ownrs) == (flatten(offsiders) + flatten(onnsiders));
}

lemma FlattenOutsideFlatten(sider : Object, pivot : Object)
  requires sider.Ready()
  requires pivot.Ready()
  requires outside(sider,pivot)
   ensures forall x <- sider.AMFO :: outside(x,pivot)
{}


lemma FlattenContainsFlatten(below : Owner, above : Owner)
  //flattening above within flatten(ownrs) is also in flatten(ownrs)
  //replaces farage
  requires AllReady(below)
  requires AllReady(above)
  requires flatten(below) >= above
   ensures forall x : Object <- above:: x.AMFO <= flatten(below)
   ensures forall x : Object <- flatten(below) :: x.AMFO <= flatten(below)
   ensures flatten(below) >= flatten(above)
{
  //  assert isFlat( flatten(below) );
  //  assert forall o <- flatten(below), oo <- o.AMFO :: oo in flatten(below);
  // assert forall o <- flatten(below) :: o.AMFO <= flatten(below);
  //  assert forall a <- above :: a in flatten(below);
  //   assert forall a <- above :: a.AMFO <= flatten(below);\
}

lemma ReadyFlatten(oo : Owner)
 requires AllReady(oo)
  ensures AllReady(flatten(oo))
{}

//is "inside_pivot" a better name than owners_inside
//{:timeLimit 20}
lemma  GordonPivotFringeInsideFlatternOwner(owners_inside_nopivot : Owner, pivot : Object, whole_f : Owner)

 requires forall i <- owners_inside_nopivot :: inside(i, pivot)
 requires owners_inside_nopivot > {}
 requires AllReady(owners_inside_nopivot)
 requires pivot.Ready()
 requires whole_f == set x  <- flatten(owners_inside_nopivot), xo <- x.owner | (outside(xo,pivot) ) :: xo
  ensures forall x  <- flatten(owners_inside_nopivot), xo <- x.owner | (outside(xo,pivot) ) :: xo in flatten(owners_inside_nopivot)
  // flatten(owners_inside_nopivot) >= (whole_f) //BUT IT's XO X!!!
  ensures flatten(owners_inside_nopivot) >= flatten(whole_f)
{
  forall x : Object <- flatten(owners_inside_nopivot), xo <- x.owner | (outside(xo,pivot) ) ensures ( xo in flatten(owners_inside_nopivot) ) //by
   {
  assert AllReady(flatten(owners_inside_nopivot));
  assert x.Ready() by {
    assert AllReady(flatten(owners_inside_nopivot));
    assert x in flatten(owners_inside_nopivot);
    assert forall q <- flatten(owners_inside_nopivot) :: q.Ready();
    assert x.Ready();
    }
  assert xo.Ready();
  assert x in flatten(owners_inside_nopivot);
  assert xo in x.owner;
    FlattenContainsFlatten(owners_inside_nopivot,x.owner);
    assert flatten(owners_inside_nopivot) >= flatten(x.owner);
    // OwnerInFlatten(owners_inside_nopivot, x, xo);
   }

  forall x <- flatten(owners_inside_nopivot), xo <- x.owner ensures flatten(owners_inside_nopivot) >= flatten({x}) >= flatten(x.owner) >= flatten({xo})
     {
    assert x.Ready() by {
        assert AllReady(flatten(owners_inside_nopivot));
        assert x in flatten(owners_inside_nopivot);
        assert forall q <- flatten(owners_inside_nopivot) :: q.Ready();
        assert x.Ready();
    }
     assert x in flatten(owners_inside_nopivot);
     assert xo in flatten(owners_inside_nopivot);
     OwnerInFlatten(owners_inside_nopivot, x, xo);
     }


 forall x <- whole_f ensures (flatten(owners_inside_nopivot) >= flatten({x}))
  {
    assert x in flatten(owners_inside_nopivot);
    FlattenContainsFlatten(owners_inside_nopivot,{x});
  }


  assert flatten(owners_inside_nopivot) >= flatten(whole_f);
}


lemma  GordonPivotFringeIsPivotOwner(owners_inside_nopivot : Owner, pivot : Object, pivot_f : Owner)

 requires forall i <- owners_inside_nopivot :: inside(i, pivot)
 requires owners_inside_nopivot > {}
 requires AllReady(owners_inside_nopivot)
 requires pivot.Ready()

 requires pivot_f == set x  <- flatten(owners_inside_nopivot), xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo
  ensures pivot_f == pivot.owner
{
assert (set x  <- flatten(owners_inside_nopivot), xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo)
          ==
       (set x : Object <- {pivot}, xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo);

assert (set x : Object <- {pivot}, xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo)
          ==
       (set xo <- pivot.owner | (inside(pivot,pivot) ) && (outside(xo,pivot) ) :: xo);

assert forall xo <- pivot.owner :: (inside(pivot,pivot) ) && (outside(xo,pivot));

assert inside(pivot,pivot);

assert forall xo <- pivot.owner :: outside(xo,pivot);

assert (set xo <- pivot.owner | (inside(pivot,pivot) ) && (outside(xo,pivot) ) :: xo)
          ==
       (set xo <- pivot.owner :: xo);

assert (set xo <- pivot.owner :: xo)
          ==
       (pivot.owner);


}


//is "inside_pivot" a better name than owners_inside
//{:timeLimit 20}
lemma {:timeLimit 20} GordonRamseyThemFringes(owners_inside_nopivot : Owner, pivot : Object) returns (whole_f : Owner, fringe : Owner, pivot_f : Owner)

 requires forall i <- owners_inside_nopivot :: inside(i, pivot)

 requires owners_inside_nopivot > {}
 requires AllReady(owners_inside_nopivot)
 requires pivot.Ready()
  ensures whole_f == set x  <- flatten(owners_inside_nopivot), xo <- x.owner |                  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo
  ensures fringe  == set x  <- flatten(owners_inside_nopivot), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo
  ensures pivot_f == set x  <- flatten(owners_inside_nopivot), xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo
  ensures pivot_f == pivot.owner
  ensures whole_f == pivot_f + fringe
  ensures whole_f == fringe + pivot.owner
  ensures flatten(owners_inside_nopivot) >= flatten(whole_f)
  ensures flatten(owners_inside_nopivot) >= flatten(fringe)
  ensures flatten(owners_inside_nopivot) >= flatten(pivot_f)
  ensures forall f <- whole_f :: (f in flatten(owners_inside_nopivot)) && outside(f,pivot)
  ensures forall f <- fringe  :: (f in flatten(owners_inside_nopivot)) && outside(f,pivot)
  ensures forall f <- pivot_f :: (f in flatten(owners_inside_nopivot)) && outside(f,pivot)
  ensures AllReady(flatten(owners_inside_nopivot))
  ensures AllReady(whole_f)
  ensures AllReady(fringe)
  ensures AllReady(pivot_f)
{
          fringe  := set x  <- flatten(owners_inside_nopivot), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
         whole_f  := set x  <- flatten(owners_inside_nopivot), xo <- x.owner |                  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
         pivot_f  := set x  <- flatten(owners_inside_nopivot), xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
     var pvtfrng  := set xo <- pivot.owner                                   |                                        (outside(xo,pivot) ) :: xo;

//
// assert WHOLEOIN: flatten(owners_inside_nopivot) >= whole_f;
// FlattenContainsFlatten(owners_inside_nopivot, whole_f);
// assert flatten(owners_inside_nopivot) >= flatten(whole_f);
//
// assert FRINFOIN: flatten(owners_inside_nopivot) >= fringe;
// FlattenContainsFlatten(owners_inside_nopivot, fringe);
// assert flatten(owners_inside_nopivot) >= flatten(fringe);


assert AllReady(owners_inside_nopivot);
ReadyFlatten(owners_inside_nopivot);
assert AllReady(flatten(owners_inside_nopivot));
assert forall x <- flatten(owners_inside_nopivot), xo <- x.owner :: x.Ready() && xo.Ready();

forall x  <- flatten(owners_inside_nopivot), xo <- x.owner ensures (whole_f == pivot_f + fringe)  //by
 {
    if (inside(x,pivot) ) && (outside(xo,pivot))
      {
        assert xo in whole_f;
        if (x == pivot) { assert xo in pivot_f;
                          assert xo in pivot.owner; }
        if (x != pivot) { assert xo in fringe; }

        assert x.Ready();
        assert xo.Ready();
        FLATTEN_OWNER2(x,xo);

      }
 }
assert whole_f >= pivot_f + fringe;
assert whole_f <= pivot_f + fringe;

//  assert forall i <- owners_inside_nopivot :: inside(i, pivot);
//  assert owners_inside_nopivot > {};
//  assert AllReady(owners_inside_nopivot);
//  assert pivot.Ready();

GordonPivotFringeIsPivotOwner(owners_inside_nopivot, pivot, set x <- flatten(owners_inside_nopivot), xo <- x.owner | (x == pivot) && (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo
);
//
// assert (set x  <- flatten(owners_inside_nopivot), xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo)
//           ==
//        (set x : Object <- {pivot}, xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo);
//
// assert (set x : Object <- {pivot}, xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo)
//           ==
//        (set xo <- pivot.owner | (inside(pivot,pivot) ) && (outside(xo,pivot) ) :: xo);
//
// assert forall xo <- pivot.owner :: (inside(pivot,pivot) ) && (outside(xo,pivot));
//
// assert inside(pivot,pivot);
//
// assert forall xo <- pivot.owner :: outside(xo,pivot);
//
// assert (set xo <- pivot.owner | (inside(pivot,pivot) ) && (outside(xo,pivot) ) :: xo)
//           ==
//        (set xo <- pivot.owner :: xo);
//
// assert (set xo <- pivot.owner :: xo)
//           ==
//        (pivot.owner);
//

 assert pivot_f == pvtfrng == pivot.owner;


  assert pivot_f == pivot.owner;
  assert whole_f == pivot_f + fringe;
  assert whole_f == fringe + pivot.owner;
//whole_f == set x <- flatten(owners_inside_nopivot), xo <- x.owner | (outside(xo,pivot) ) :: xo
  GordonPivotFringeInsideFlatternOwner(owners_inside_nopivot, pivot, set x <- flatten(owners_inside_nopivot), xo <- x.owner | (outside(xo,pivot) ) :: xo);

  assert flatten(owners_inside_nopivot) >= flatten(whole_f);
  assert flatten(owners_inside_nopivot) >= flatten(fringe);
  assert flatten(owners_inside_nopivot) >= flatten(pivot_f);
  assert forall f <- whole_f :: (f in flatten(owners_inside_nopivot)) && outside(f,pivot);
  assert forall f <- fringe  :: (f in flatten(owners_inside_nopivot)) && outside(f,pivot);
  assert forall f <- pivot_f :: (f in flatten(owners_inside_nopivot)) && outside(f,pivot);





forall x <- flatten(owners_inside_nopivot), xo <- x.owner ensures (whole_f == pivot_f + fringe) {
  assert x.Ready();
  assert xo.Ready();

 if ( (inside(x,pivot) ) && (outside(xo,pivot) ) )
   {
    assert xo in whole_f;
    if (x == pivot)
      {
         assert xo in pivot_f;
         assert xo in pvtfrng;
         assert xo in pivot.owner;
         assert pivot_f == pvtfrng == pivot.owner;
      } else {
         assert xo in fringe;
         //assert pivot_f == pvtfrng;
      }
      assert (xo in pivot_f) || (xo in fringe);
      assert whole_f == pivot_f + fringe;
    //  assert pivot_f == pvtfrng == pivot.owner;

   } //end if


}//end foreach

  assert whole_f == fringe + pivot_f;
  assert whole_f == fringe + pivot.owner;


  // FlattenContainsFlatten(owners_inside_nopivot, fringe) by
  //   { assert fringe <= flatten(owners_inside_nopivot) by { reveal FRINFOIN; } }

}//end GordonRamsey

///FUCK FCUK FUCK
lemma FlattenFringeIsAllOutside(iwnrs : OWNR,  pivot : Object) returns (allInside : Owner, allOutside : Owner, fringe : Owner)
   ///used in tiredOfSleeping... so need to worry
  //ensuress flatten(fringe) == allOutside
  //all iwnrs must all be strictlyInside pivot????
  //pretty much the wrong thing cons iwnrs != owners != ownrs != onnsiders...
  //iwnrs better be equal to owners_Inside???
  //note - works OK if iwners == {}.   just take the pibot out ogf owners_inside before calling this.
 requires forall i <- iwnrs :: strictlyInside(i, pivot)
  //or coudl do it here I gues...

 requires AllReady(flatten(iwnrs))
 requires pivot.Ready()

    ensures allInside  == set x <- flatten(iwnrs) | inside(x, pivot)
    ensures allOutside == set x <- flatten(iwnrs) | outside(x, pivot)
  ensures allInside !! allOutside
  ensures flatten(iwnrs) == (allInside + allOutside)
  //  ensures fringe ==  set x <- allInside, xo <- x¸ | (xo in allOutside)  :: xo

  ensures fringe == set x <- flatten(iwnrs), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo

  ensures iwnrs <= allInside
  ensures forall o <- allInside  :: o.owner <= (allInside + allOutside)
  ensures forall o <- allOutside :: o.owner <= allOutside
  ensures fringe == set x <- allInside, xo <- x.owner | (x != pivot) &&   (xo in allOutside)  :: xo //original version
//  ensures forall o <- flatten(iwnrs), oo <- o.owner :: (o != pivot) &&  (inside(o,pivot) ) && (outside(oo,pivot) )
  ensures fringe <= allOutside
  ensures flatten(fringe) <= allOutside
  //ensures (flatten(fringe) + flatten({pivot})) == allOutside
{

  allInside  := set x <- flatten(iwnrs) | inside(x, pivot);
  allOutside := set x <- flatten(iwnrs) | outside(x, pivot);

//for nightly?
 forall x <- flatten(iwnrs) ensures flatten(iwnrs) == (allInside + allOutside) //by
  {
    if inside(x, pivot) { assert x in allInside; } else { assert outside(x, pivot); assert x in allOutside; }
  }


 //old fringe := set x <- allInside, xo <- x.owner | (xo in allOutside)  :: xo;
 //opt fringe := set x <- allInside, xo <- x.owner |  (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
   fringe := set x <- flatten(iwnrs), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
 assert fringe == set x <- allInside, xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
  assert fringe <= allOutside;
  OUTSIDE_OUTSIDE(fringe, pivot);
  assert forall f <- flatten(fringe) :: outside(f,pivot);
  assert forall f <- flatten(fringe) :: f in flatten(iwnrs);
  assert flatten(fringe) <= allOutside;

  assert forall t <- allOutside :: t in flatten(iwnrs);


  forall t <- allOutside ensures (t in (flatten(fringe) + flatten({pivot})))   // (t in flatten(fringe)) //(t in flatten(fringe))  //by
  {
    forall part <- iwnrs | (t in flatten({part})) ensures (t in (flatten(fringe) + flatten({pivot}))) {
      var prev, next := AcrossTheBorder(part, pivot, t);
      assert strictlyInside(prev,t);
      assert not(strictlyInside(next,pivot)); //ORIG
      assert prev in flatten(iwnrs);
      assert next in prev.owner;
      assert prev in allInside;
      assert (next in allOutside) || (next == pivot);
      assert (next in fringe) || (next == pivot);
      assert t in flatten(iwnrs);
      assert t in next.AMFO;
      assert t in flatten({next});
      if (next in fringe) { assert t in flatten(fringe); }
       else { assert next == pivot; assert t in flatten({pivot}); }
      assert t in (flatten(fringe) + flatten({pivot}));
    }
  }

  assert (flatten(fringe) + flatten({pivot})) >= allOutside;
//  assert (flatten(fringe) + flatten({pivot})) == allOutside;

}





lemma Notin(ownrs : OWNR,  pivot : Object, allInside : Owner, allOutside : Owner, fringe : Owner)
  //proof by contradiction
  //pivot is not in rest of fringe
  //was going to extend to an "OnlyTHrough" apparently
  requires AllReady(flatten(ownrs))
  // requires pivot.Ready()
  requires allInside  == set x <- flatten(ownrs) | strictlyInside(x, pivot)
  requires allOutside == set x <- flatten(ownrs) | not(strictlyInside(x, pivot))
  // requires allInside !! allOutside
  // requires flatten(ownrs) == (allInside + allOutside)
  requires fringe == set x <- allInside, xo <- x.owner | (xo in allOutside)  :: xo
  // requires fringe <= allOutside
  //requires (allInside > {}) ==> (flatten(fringe) == allOutside)
  //requires (allInside > {}) ==> (pivot in fringe)

  ensures pivot !in flatten(fringe - {pivot})
{
  if (pivot in flatten(fringe - {pivot})) {
    assert not(fringe <= allOutside);
    assert false;
  }
}



lemma {:resource_limit 70000000}  {:timeLimit 20} splitOwnersAroundPivot(part : Object, pivot : Object) returns (allInside : Owner, allOutside : Owner, fringe : Owner)
  //splits all into the bits inside pivot,
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
  //rensures flatten(fringe) + flatten({pivot}) == allOutside
  //ensures flatten(fringe - {pivot}) + flatten({pivot}) == flatten(fringe) == allOutside

  //ensures all == recOwners(part)  //can do with Axioms from Ownership-Parallel if necessary...

{
  var all := part.AMFO;

  allInside  := set x <- all | strictlyInside(x, pivot);
  assert part in allInside;

  allOutside := all - allInside;
  assert forall x <- allOutside :: not(strictlyInside(x, pivot));
  assert pivot in allOutside;

  assert forall x <- all :: strictlyInside(x, pivot) != not(strictlyInside(x, pivot));

  assert allInside !! allOutside;
  assert all == (allInside + allOutside);

  fringe := set x <- all, xo <- x.owner | (x in allInside) && (xo in allOutside)  :: xo;
  assert fringe <= allOutside;
  assert fringe == set x <- allInside, xo <- x.owner | (xo in allOutside)  :: xo;

  assert part !in fringe;
  //   assert exists x <- allInside, xo <- x.owner ::  xo == pivot;

  var prev := YouGetThereEventually(part, pivot);
  assert pivot in prev.owner;
  assert strictlyInside(prev,pivot);
  assert prev in all;
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
    assert prev in all;
    assert next in prev.owner;
    assert prev in allInside;
    assert next in allOutside;
    assert next in fringe;
    assert t in all;
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
//  assert flatten(fringe - {pivot}) + flatten({pivot}) == flatten(fringe) == allOutside;
//  assert flatten(fringe) + flatten({pivot}) == allOutside;
}




lemma AcrossTheBorder(part : Object,  pivot : Object, whole : Object) returns (prev : Object, next : Object)
  //returns two transitive owners of part that on the way to whole, where prev is inside pivot, and next is outside or == pivot
  decreases part.AMFO
   requires part.Ready()
   requires whole.Ready()
   requires pivot.Ready()
   requires strictlyInside(part, whole)
   requires strictlyInside(part, pivot)
 //requires inside(part, pivot)  //REVERT
   requires not(strictlyInside(whole, pivot))

    ensures part != whole
    ensures prev in part.AMFO
    ensures next in part.AMFO
    ensures inside(part,prev)
    ensures strictlyInside(part,next)
    ensures strictlyInside(prev,pivot)
    ensures strictlyInside(prev,whole)
    ensures next in prev.owner
    ensures not(strictlyInside(next,pivot))
    ensures outside(next,pivot) || (next == pivot)
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
    invariant pivot.Ready()
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

//makerfield({next}, pivot);

  assert not(strictlyInside(next,pivot));
  BLAH_BLAH_BLAH(next,pivot);
  assert outside(next,pivot) || (next == pivot);
}

lemma BLAH_BLAH_BLAH(a : Object, b : Object)
 requires a.Ready()
 requires b.Ready()
 requires not(strictlyInside(a,b))
  ensures not(a.AMFO > b.AMFO)
  ensures not( (a.AMFO >= b.AMFO) && not(a.AMFO == b.AMFO) )
  ensures not( (a.AMFO >= b.AMFO) )  ||  (a.AMFO == b.AMFO)
  ensures not( inside(a,b) ) || (a == b)
  ensures outside(a,b)       || (a == b)
{AXIOMAMFOS(a,b);}

lemma OUTSIDE_OUTSIDE(oo : Owner, pivot : Object)
 requires AllReady(oo)
 requires pivot.Ready()
 requires forall o <- oo          :: outside(o, pivot)
  ensures forall o <- flatten(oo) :: outside(o, pivot)
{}


lemma {:verify false} XPivotInFringe(ownrs : OWNR, pivot : Object, probe : Object)
     //except the Pivot is no longer in the Fringe
  decreases probe.AMFO
  requires AllReady(flatten(ownrs))

  requires probe.Ready()
  requires pivot.Ready()
  requires strictlyInside(probe, pivot)
  requires probe != pivot
  requires exists o <- ownrs :: strictlyInside(o,pivot)

   ensures pivot in fFringe(ownrs, pivot)
{
   var prev := YouGetThereEventually(probe, pivot);
    assert pivot in prev.owner;
    assert strictlyInside(prev,pivot);

    assert prev  in fInside(ownrs, pivot);
    assert pivot in fOutside(ownrs, pivot);
    assert pivot in fFringe(ownrs, pivot);
}



lemma OwnerInFlatten(xwrns : OWNR, x : Object, xo : Object)
  requires AllReady(flatten(xwrns))
  requires x.Ready()
  requires xo.Ready()

  requires x in flatten(xwrns)
  requires xo in x.owner

  ensures xo in flatten(xwrns)
  ensures flatten(xwrns) >= flatten({x})
  ensures flatten(xwrns) >= flatten({xo})
{
FlattenContainsFlatten(xwrns, {x});
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
  ensures inside(part, prev)
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
    assert prev in part.AMFO;
    return;
  }
  prev := YouGetThereEventually(prev, whole);
}


// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // ////
/// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // ///


//
// lemma {:timeLimit 30} LetMeBeYourLighthouseKeeper(below : OWNR, above : OWNR)
//   //at least one of below's direct owners is on the way to above.
//   requires AllReady(below) && isFlat(below)
//   requires AllReady(above) && isFlat(above)
//   requires below >= above
//   ensures (below == above) || (exists x <- below :: x.AMFO >= above)
//  {
//     if (below == above) {
//       assert ((below == above) || (exists x <- below :: x.AMFO >= above));
//       return; }
//
//     assert below != above;
//     assert (exists x <- below :: x.AMFO >= above);
//  }



//
lemma {:timeLimit 30} ThereIsALightThatNeverGoesOut(part : Object, whole : Object)
  //at least one of part's direct owners is on the way to whole.
  requires part.Ready()
  requires whole.Ready()
  requires inside(part,whole)
  ensures (part == whole) || (exists x <- part.owner :: inside(x, whole))
{
  //    InsideRecInside2(part, whole);

  if (part == whole) {
    assert ((part == whole) || (exists x <- part.owner :: inside(x, whole)));
    return; }

  assert part != whole;
  assert (exists x <- part.owner :: inside(x,whole));
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









lemma FLATTEN_SUBS(a : Owner, b : Owner)
  requires a >= b
  ensures flatten(a - b) + flatten(b) == flatten(a)
{}

lemma FLATTEN_SUM3(a : Owner, b : Owner, c : Owner)
  requires a+b == c
  ensures flatten(a) + flatten(b) == flatten(a+b)
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




lemma OH_FUCK_WHAT_HAVE_I_DONE(oo : Owner, m : Klon) returns (sp : Owner)
  decreases allAMFOs(oo)
  requires AllReady(oo)
  requires klonReady(m)
  requires klonCalid(m)
  requires oo <= m.m.Keys
{
  var rsp := recSplatten(oo,m);
  var fmk := flatten(mapThruKlon(oo,m));
  var mkf := mapThruKlon(flatten(oo),m);

  assert rsp == fmk;
  sp := oo;
}



lemma {:timeLimit 30} recSplatten(oo : Owner, m : Klon) returns (sp : Owner)
   ///predicts flatten(mapThruKlon(oo, m))

  decreases allAMFOs(oo)
  requires AllReady(oo)
  requires klonReady(m)
  requires klonCalid(m)
  requires oo <= m.m.Keys
//requires exists x <- oo :: inside(x, m.o)

  ensures flatten(oo) <= m.m.Keys
  ensures sp == flatten(mapThruKlon(oo, m))
  ensures AllReady(sp)
  ensures (exists x <- oo :: inside(x, m.o)) ==>
     (exists x <- oo :: inside(x, m.o) && (x in m.m.Keys) && (m.m[x] in sp) && inside(m.m[x],m.c))

{
  //     var x :=  {set o : Object <- oo, ooo <- recOwners(o) :: ooo};

  sp := {};

  var todo := oo;
  var done : Owner := {};
  assert AllReady(todo);
  assert oo - todo == {};
  assert oo == done + todo;
  assert mapThruKlon({}, m) == {};
  assert mapThruKlon((oo - todo), m) == {};
  assert flatten({}) == {};
  assert flatten(mapThruKlon((oo - todo), m)) == {};

  assert sp == flatten(mapThruKlon((oo - todo), m));
  assert done == oo - todo == {}; assert done !! todo;
  assert sp == flatten(mapThruKlon((done), m));

  while (todo > {})
    decreases todo
    invariant sp == flatten(mapThruKlon((oo - todo), m))
    invariant done == oo - todo
    invariant sp == flatten(mapThruKlon((done), m))
//invariant exists x <- oo :: inside(x, m.o)
    invariant oo == done + todo
    invariant done !! todo
//invariant exists x <- (done + todo) :: inside(x, m.o)
    invariant forall x <- done | inside(x,m.o) ::  inside(m.m[x],m.c) && (m.m[x] in sp)
  {
    assert sp == flatten(mapThruKlon((oo - todo), m));

    var next :| next in todo;
    assert done == oo - todo;

    var todoHERE := todo;
    assert ttt: next in todo;
    assert nit: next in todoHERE;
    assert done !! todo;
    assert next !in done;
    assert todo == todoHERE;
    assert done == oo - todoHERE;
    assert oo == done + todo == done + todoHERE;

    assert todo decreases to todo - {next} by { reveal ttt; }

    todo := todo - {next};
    assert next !in todo;
    assert next !in done;
    assert done !! {next} !! todo;

    assert next in todoHERE by { reveal nit; }
    assert todo == todoHERE - {next};
    MINUS3(todo,todoHERE,{next});
    assert todoHERE == todo + {next};

    assert oo == done + todo ;
    assert done !! {next} !! todo;
    assert oo == done + (todo + {next});

    assert done == oo - todoHERE;
    assert todoHERE == todo + {next};
    assert done == oo - (todo + {next});
    PLUS_MINUS(done,oo,todo,{next});
    assert done == oo - todo - {next};



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

    assert oo == done + (todo + {next});
    assert done !! {next} !! todo;
    PLUS4(oo, done, todo, {next});
    assert oo == (done + {next}) + todo;

    done := done + {next};
    assert oo == done + todo;
    assert done == oo - todo;
    assert sp == flatten(mapThruKlon((done), m));
    assert sp == flatten(mapThruKlon((oo - todo), m));
  }//end while


  assert sp == flatten(mapThruKlon((oo - todo), m));
  assert oo == done + todo;
  assert done == oo - todo;
  assert todo == {}; assert done == oo;
  assert sp == flatten(mapThruKlon(oo, m));


//  assert exists x <- oo   | inside(x, m.o) :: inside(m.m[x], m.c);
  assert forall x <- done | inside(x,m.o) ::  inside(m.m[x],m.c) && (m.m[x] in sp);
//  assert exists y <- sp  :: inside(y,m.c) && (y in sp);
  }//end recSplatteno





lemma {:timeLimit 50} insideThruKlon(below : Owner, above : Owner, m : Klon) returns (selow : Owner,  sbove : Owner)
  decreases allAMFOs(below)
  requires AllReady(below)
  requires AllReady(above)

  requires AllReady(flatten(below))
  requires m.o.Ready()
  requires flatten(below) >= m.o.AMFO           //hmm
  requires exists x <- below :: inside(x, m.o)  //hmm
  requires xbi: exists x <- below :: inside(x, m.o)  //hmm


  requires AllReady(flatten(above))
  requires m.o.Ready()
  requires flatten(above) >= m.o.AMFO           //hmm
  requires exists x <- above :: inside(x, m.o)  //hmm

  requires klonReady(m)
  requires klonCalid(m)
  requires below <= m.m.Keys
  requires above <= m.m.Keys
  requires flatten(below) >= flatten(above)
   ensures flatten(selow) >= flatten(sbove)
   {
  var pivot := m.o;

  var left := recSplatten(below, m);
  var rift := recSplatten(above, m);

  var li,lo,lb,lf := tiredOfSleeping(left, pivot) by { reveal xbi; assert exists x <- below :: inside(x, m.o); } //hmm
  var ri,ro,rb,rf := tiredOfSleeping(rift, pivot);

  assert flatten(left) == flatten(lo) + lb + flatten(lf) + pflivot(left, pivot);
  assert flatten(rift) == flatten(ro) + rb + flatten(rf) + pflivot(rift, pivot);

  assert flatten(lo) >= flatten(ro);
  assert lb == rb;
  assert flatten(lf) >=  flatten(rf);
  assert flatten(left) >= flatten(rift);
  // assert selow  ==
  //  ((flatten(lo) >= flatten(ro)) && (lb >= rb) && (flatten(lf) >= flatten(rf)));

   selow := left;
   sbove := rift;
  }

//reminder OWNR is flat
lemma {:verify false} old_insideThruKlon(below : Owner, above : Owner, m : Klon) returns (rv : bool)
  decreases allAMFOs(below)
  requires AllReady(below)
  requires AllReady(above)
  requires klonReady(m)
  requires klonCalid(m)
  requires below <= m.m.Keys
  requires above <= m.m.Keys

  requires flatten(below) >= flatten(above)
{
  var pivot := m.o;

  var belowFlat : OWNR := recSplatten(below, m);
  var aboveFlat : OWNR := recSplatten(above, m);


  var belowInside,belowOutside,belowFringe := XsplitOWNRSroundPivot(below, pivot);
  assert (belowInside > {}) ==> (pivot in belowFringe);
  var belowFringeNoPivot := belowFringe - {pivot};

  var aboveInside,aboveOutside,aboveFringe := XsplitOWNRSroundPivot(above, pivot);
  assert (aboveInside > {}) ==> (pivot in aboveFringe);
  var aboveFringeNoPivot := aboveFringe - {pivot};



  rv := (belowFlat >= aboveFlat);
  assert rv;
}


lemma PLUS_MINUS(a : Owner, b : Owner, c : Owner, d : Owner)
  requires a == b - (c + d)
   ensures a == b - c - d
{}

lemma MINUS3(a : Owner, b : Owner, c : Owner)
  requires c <= b
  requires a == b - c
   ensures b == a + c
{}

lemma PLUS4(a : Owner, b : Owner, c : Owner, d : Owner)
  requires a == b + (c + d)
  requires b !! c !! d
   ensures a == (b + d) + c
{}
