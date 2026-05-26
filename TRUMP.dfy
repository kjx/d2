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
 //given aliaes in flattern(ownrs), faltten(alianes) in flattern(owners)
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


lemma {:timeLimit 30} makersfield(ownrs : OWNR, pivot : Object)
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()
  ensures forall x <- ownrs ::    (x.AMFO >= pivot.AMFO) != (not(x.AMFO >= pivot.AMFO))
  ensures forall x <- ownrs :: not(x.AMFO >= pivot.AMFO) != not(not(x.AMFO >= pivot.AMFO))
  ensures forall x <- ownrs ::          outside(x,pivot) != not(outside(x,pivot))
  ensures forall x <- ownrs ::           inside(x,pivot) != not( inside(x,pivot))
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
lemma BROKEN_insidesFlattenFringe(ownrs : OWNR, pivot : Object) returns (allInside : Owner, allOutside : Owner, fringe : Owner)
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

lemma {:timeLimit 60} FLATTEN_SYRINGE(ownrs : OWNR, pivot : Object)
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


lemma justTiredAncientsOfMuMu()



//{:timeLimit 7}
lemma  tiredOfSleeping(owner : Owner, pivot : Object)
  returns (owners_inside : Owner, owners_outside : Owner, flat_below : Owner, fringe : Owner)
  //FUCK,. shoudl this be a function?  or indeed series of functions?
  //pivot or Klon??
  requires AllReady(flatten(owner))
  requires pivot.Ready()     requires piR: pivot.Ready()

  ensures owners_inside ==  set x <- owner |  inside(x, pivot)
  ensures owners_outside == set x <- owner | outside(x, pivot)
  ensures owner == owners_outside + owners_inside
  ensures flatten(owner) == flatten(owners_inside) + flatten(owners_outside)

  ensures flat_below == set x <- flatten(owners_inside) | inside(x,pivot)   ///pivot will be inside
  ensures fringe == set x <- flatten(owners_inside), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo

//  ensures flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + flatten({pivot})
{
  owners_inside, owners_outside := SplitTheDeadOwners(owner, pivot);

  if (owners_inside == {})
  {
    flat_below := {}; fringe := {}; return;
    //a more dedicated model could do more here, but not needed for correctness
  }

  assert owners_inside > {};

  flat_below := set x <- flatten(owners_inside) | inside(x,pivot);   ///pivot will be inside
  var flat_above := set x <- flatten(owners_inside) | outside(x,pivot);
  assert flatten(owners_inside) == flat_below + flat_above;

var flatI,flatO,fw := FlattenFringeIsAllOutside(owners_inside,pivot);
assert flatten(fw) == flatO;

assert flatI == flat_below;
assert flatO == flat_above;

        fringe := set x  <- flatten(owners_inside), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
  var whole_f  := set x  <- flatten(owners_inside), xo <- x.owner |                  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
  var pivot_f  := set x  <- flatten(owners_inside), xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
  var pvtfrng  := set xo <- pivot.owner                           |                                        (outside(xo,pivot) ) :: xo;


assert fw == whole_f;
assert flatten(whole_f) == flat_above;

assert (set x  <- flatten(owners_inside), xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo)
          ==
       (set x : Object <- {pivot}, xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo);

assert (set x : Object <- {pivot}, xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo)
          ==
       (set xo <- pivot.owner | (inside(pivot,pivot) ) && (outside(xo,pivot) ) :: xo);

assert forall xo <- pivot.owner :: (inside(pivot,pivot) ) && (outside(xo,pivot));

assert (set xo <- pivot.owner | (inside(pivot,pivot) ) && (outside(xo,pivot) ) :: xo)
          ==
       (set xo <- pivot.owner :: xo)
          ==
       (pivot.owner);


 assert pivot_f == pvtfrng == pivot.owner;

forall x <- flatten(owners_inside), xo <- x.owner ensures (whole_f == pivot_f + fringe) {
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

  assert flatten(whole_f) == flat_above;
  assert flatten(fringe + pivot.owner) == flat_above;
  assert flatten(fringe) + flatten(pivot.owner) == flat_above;

  assert flat_above == flatten(fringe + pivot.owner);
  assert flat_above == flatten(fringe) + flatten(pivot.owner);

  assert flatten({pivot}) == {pivot} + flatten(pivot.owner);
  assert flat_above == flatten(fringe) + flatten(pivot.owner);
  assert flat_above + {pivot} == flatten(fringe) + flatten({pivot});

  assert pivot in flat_below;
  assert flat_below + flat_above == flat_below + flatten(fringe) + flatten({pivot});


  assert flatten(owners_inside) == flat_below + flat_above;
  assert flatten(owners_inside) == flat_below + flatten(fringe) + flatten({pivot});

  assert flatten(owner) == flatten(owners_outside) + flatten(owners_inside);
  assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + flatten({pivot});
}



datatype Segmented = Segmented(owner : Owner,  rat : nat)


//{:timeLimit 30}   {:timeLimit 60} {:timeLimit 120}
lemma {:timeLimit 7} shouldBeSleeping(ownrs : OWNR, pivot : Object) returns (onnsiders : Owner, offsiders : Owner, allInside : Owner, allOutside : Owner, fringe : Owner)
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
lemma {:timeLimit 120} splitOWNRSroundPivot(ownrs : OWNR, pivot : Object) returns (allInside : Owner, allOutside : Owner, fringe : Owner)
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

  PivotInFringe(ownrs, pivot, probe);

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


  // makersfield(ownrs, pivot);

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

  makersfield(ownrs, pivot);

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
  requires AllReady(below)
  requires AllReady(above)
  requires flatten(below) >= above
  ensures flatten(below) >= flatten(above)
{
  //  assert isFlat( flatten(below) );
  //  assert forall o <- flatten(below), oo <- o.AMFO :: oo in flatten(below);
  // assert forall o <- flatten(below) :: o.AMFO <= flatten(below);
  //  assert forall a <- above :: a in flatten(below);
  //   assert forall a <- above :: a.AMFO <= flatten(below);
}


lemma FlattenFringeIsAllOutside(iwnrs : OWNR,  pivot : Object) returns (allInside : Owner, allOutside : Owner, fringe : Owner)
  //ensuress flatten(fringe) == allOutside
  //all iwnrs must all be strictlyInside piot
  //pretty much the wrong thing cons iwnrs != owners != ownrs != onnsiders...

 requires forall i <- iwnrs :: inside(i, pivot)

 requires AllReady(flatten(iwnrs))
 requires pivot.Ready()

  ensures allInside  == set x <- flatten(iwnrs) | inside(x, pivot)
  ensures allOutside == set x <- flatten(iwnrs) | outside(x, pivot)
  ensures allInside !! allOutside
  ensures flatten(iwnrs) == (allInside + allOutside)
  ensures fringe == set x <- allInside, xo <- x.owner | (xo in allOutside)  :: xo

  ensures iwnrs <= allInside
  ensures forall o <- allInside  :: o.owner <= (allInside + allOutside)
  ensures forall o <- allOutside :: o.owner <= allOutside
  ensures forall o <- allInside, oo <- o.owner ::  (oo in allOutside) == (oo in fringe)
  ensures fringe <= allOutside
  ensures flatten(fringe) == allOutside
{

  allInside  := set x <- flatten(iwnrs) | inside(x, pivot);
  allOutside := set x <- flatten(iwnrs) | outside(x, pivot);
  fringe := set x <- allInside, xo <- x.owner | (xo in allOutside)  :: xo;

  assert fringe <= allOutside;
  assert flatten(fringe) <= allOutside;

  assert forall t <- allOutside :: t in flatten(iwnrs);

  forall t <- allOutside ensures (t in flatten(fringe)) //(t in flatten(fringe))  //by
  {
    forall part <- iwnrs | (t in flatten({part})) ensures (t in flatten(fringe)) {
      var prev, next := AcrossTheBorder(part, pivot, t);
      assert strictlyInside(prev,t);
      assert not(strictlyInside(next,pivot));
      assert prev in flatten(iwnrs);
      assert next in prev.owner;
      assert prev in allInside;
      assert next in allOutside;
      assert next in fringe;
      assert t in flatten(iwnrs);
      assert t in next.AMFO;
      assert t in flatten({next});
      assert t in flatten(fringe);
    }
  }

  assert flatten(fringe) >= allOutside;
  assert flatten(fringe) == allOutside;

}



lemma OnlyThrough(ownrs : OWNR,  pivot : Object,  allInside : Owner, allOutside : Owner, fringe : Owner)
  //proof by contradiction?
  //to get from ownrs thru pivot to outside you must go through fringe x
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()
  requires allInside  == set x <- flatten(ownrs) | strictlyInside(x, pivot)
  requires allOutside == set x <- flatten(ownrs) | not(strictlyInside(x, pivot))
  requires allInside !! allOutside
  requires flatten(ownrs) == (allInside + allOutside)
  requires fringe == set x <- allInside, xo <- x.owner | (xo in allOutside)  :: xo
  requires fringe <= allOutside
  //requires (allInside > {}) ==> (flatten(fringe) == allOutside)
  requires (allInside > {}) ==> (pivot in fringe)

  ensures pivot !in flatten(fringe - {pivot})
{
  if (pivot in flatten(fringe - {pivot})) {
    assert not(fringe <= allOutside);
    assert false;
  }
}




lemma Notin(ownrs : OWNR,  pivot : Object, allInside : Owner, allOutside : Owner, fringe : Owner)
  //proof by contradiction
  //pivot is not in rest of fringe
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
  ensures flatten(fringe - {pivot}) + flatten({pivot}) == flatten(fringe) == allOutside

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
  assert flatten(fringe - {pivot}) + flatten({pivot}) == flatten(fringe) == allOutside;
}




lemma AcrossTheBorder(part : Object,  pivot : Object, whole : Object) returns (prev : Object, next : Object)
  //returns two transitive owners of part that on the way to whole, where prev is inside pivot, and next is outside or == pivot
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
  ensures strictlyInside(prev,whole)
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




lemma PivotInFringe(ownrs : OWNR, pivot : Object, probe : Object)
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



lemma OwnerInFlatten(xwrns : OWNR, a : Object, b : Object)
  requires AllReady(flatten(xwrns))
  requires a.Ready()
  requires b.Ready()

  requires a in flatten(xwrns)
  requires b in a.owner

  ensures b in flatten(xwrns)
{}




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

// ghost function claudeSplatten(oo: Owner, m: Klon): Owner
//      reads m.hns()
//  decreases allAMFOs(oo)
//   requires AllReady(oo)
//   requires klonReady(m)
//   requires klonCalid(m)
//   requires oo <= m.m.Keys
//   ensures flatten(oo) <= m.m.Keys
//   ensures recSplatten(oo, m) == flatten(mapThruKlon(oo, m))
// {
//   if oo == {} then {}
//   else
//     var next :| next in oo;
//     var sext := m.m[next];
//     var fowner :=
//       if next == m.o then flatten(m.clowner)
//       else if outside(next, m.o) then flatten(next.owner)
//       else recSplatten(next.owner, m);
//       assert next in oo;
//       assert allAMFOs(oo) decreases to allAMFOs(oo - {next});
//     ({sext} + fowner) + recSplatten(oo - {next}, m)
// }



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





//reminder OWNR is flat



lemma insideThruKlon(below : Owner, above : Owner, m : Klon) returns (rv : bool)
  decreases allAMFOs(below)
  requires AllReady(below)
  requires AllReady(above)
  requires klonReady(m)
  requires klonCalid(m)
  requires below <= m.m.Keys
  requires above <= m.m.Keys

  requires flatten(below) >= flatten(above)
  //    ensures rv
{
  var pivot := m.o;

  var belowFlat : OWNR := recSplatten(below, m);
  var aboveFlat : OWNR := recSplatten(above, m);


  var belowInside,belowOutside,belowFringe := splitOWNRSroundPivot(below, pivot);
  assert (belowInside > {}) ==> (pivot in belowFringe);
  var belowFringeNoPivot := belowFringe - {pivot};

  var aboveInside,aboveOutside,aboveFringe := splitOWNRSroundPivot(above, pivot);
  assert (aboveInside > {}) ==> (pivot in aboveFringe);
  var aboveFringeNoPivot := aboveFringe - {pivot};



  rv := (belowFlat >= aboveFlat);
  assert rv;
}
