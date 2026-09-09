include "Ownership.dfy"
include "Set-Lemmata.dfy"

//TO GET MY HEAD STRAIGHT/
//IN THIS FILE

//collectAllStrictlyInside -> collectAllStrictlyInside
//skipX -> collectX

//pretty sure the main point of this entire file
//is to prove that collectAllStrictlyInside(o,pivot) == arghStrictlyInside)(o,pivot)
//i.e,.                                   == allStrictlyInside(argh(o),pivot)
//
// skip all inside is recursive & terminates early;
//  allStrictlyInside is iteraative sugar for a set comprehension.
//
//   assert (set x <- next.AMFO | strictlyInside(x,m.o)) == collectAllStrictlyInside(next,m.o);
//   assert (set x <- cext.AMFO | strictlyInside(x,m.c)) == collectAllStrictlyInside(cext,m.c);


lemma LEMMA_INSIDE_OUTSIDE(oo : Owner, pivot : Object)
  requires AllReady(oo)
  requires pivot.Ready()
   ensures forall o <- oo :: inside(o, pivot) != outside(o, pivot)
   ensures forall o <- oo :: strictlyInside(o, pivot) != (outside(o, pivot)  || (o == pivot))
   ensures forall o <- oo :: strictlyInside(o, pivot) != pivotlyOutside(o, pivot)
{}


function collectAllStrictlyInside(o : Object, pivot : Object) : (rv : set<Object>)
  // all o's transitive owners that are strictly inside pivot
  // recursive, shortcutting analogue of allInside
  decreases o.AMFO
   requires o.Ready()
    {
      if (not(strictlyInside(o,pivot))) then ({})
          else  {o} + (set oo <- o.owner, ooo <- collectAllStrictlyInside(oo, pivot) :: ooo)
    }

function uncollectAllStrictlyInside(o : Object, pivot : Object) : (rv : set<Object>)
  // all o's transitive owners that are strictly inside pivot
  // recursive, NON-shortcutting analogue of allInside - collectAllStrictlyInside
    decreases o.AMFO
   requires o.Ready()
    {
      if (not(strictlyInside(o,pivot)))
          then        (set oo <- o.owner, ooo <- uncollectAllStrictlyInside(oo, pivot) :: ooo)
          else  {o} + (set oo <- o.owner, ooo <- uncollectAllStrictlyInside(oo, pivot) :: ooo)
    }



//======================================================================
//======================================================================
//======================================================================

function collectAllPivotlyOutside(o : Object, pivot : Object) : (rv : set<Object>)
  // all o's transitive owners that are the pivot or outside pivot
  // recursive, shortcutting analogue of allInside
  decreases o.AMFO
   requires o.Ready()
    {
      if (pivotlyOutside(o,pivot)) then (o.AMFO)
          else (set oo <- o.owner, ooo <- collectAllPivotlyOutside(oo, pivot) :: ooo)
    }

function uncollectAllPivotlyOutside(o : Object, pivot : Object) : (rv : set<Object>)
  // all o's transitive owners that are the pivot or outside pivot
  // recursive, NON-shortcutting analogue of allInside - collectAllPivotlyOutside
    decreases o.AMFO
   requires o.Ready()
    {
      if (not(pivotlyOutside(o,pivot)))
          then        (set oo <- o.owner, ooo <- uncollectAllPivotlyOutside(oo, pivot) :: ooo)
          else  {o} + (set oo <- o.owner, ooo <- uncollectAllPivotlyOutside(oo, pivot) :: ooo)
    }


function uFE_body(o : Object, pivot : Object) : (rv : set<Object>)
    decreases o.AMFO
   requires o.Ready()
    requires pivot.Ready()
    { (set oo <- o.owner, ooo <- uncollectFcckingEverything(oo, pivot) :: ooo) }

lemma LEMMA_uFE_body(o : Object, pivot : Object, rv : set<Object>)
    decreases o.AMFO
   requires o.Ready()
    requires pivot.Ready()
    requires rv ==  uFE_body(o,pivot)
     ensures rv == (set oo <- o.owner, ooo <- uncollectFcckingEverything(oo, pivot) :: ooo)
    {
      assert rv ==  uFE_body(o,pivot);
      assume rv == (set oo <- o.owner, ooo <- uncollectFcckingEverything(oo, pivot) :: ooo);
      assert rv == (set oo <- o.owner, ooo <- uncollectFcckingEverything(oo, pivot) :: ooo);
     }


lemma {:timeLimit 30} LEMMA_uFE(o : Object, pivot : Object, rv : set<Object>)
    decreases o.AMFO
   requires o.Ready()
    requires pivot.Ready()
    requires rv ==  uncollectFcckingEverything(o,pivot)
//     ensures rv ==  {o} + (set oo <- o.owner, ooo <- uncollectAllPivotlyOutside(oo, pivot) :: ooo)
    {
      assert rv == uncollectFcckingEverything(o,pivot);
      assert rv == if (true) then ({o} + uFE_body(o,pivot)) else ({o} + uFE_body(o,pivot));
      assert rv == {o} + uFE_body(o,pivot);
      assert uFE_body(o,pivot) == (set oo <- o.owner, ooo <- uncollectFcckingEverything(oo, pivot) :: ooo);
      assert rv == {o} + (set oo <- o.owner, ooo <- uncollectFcckingEverything(oo, pivot) :: ooo);
    }


function uncollectFcckingEverything(o : Object, pivot : Object) : (rv : set<Object>)
  // all o's transitive owners recursively.  so just collectAllOwners or some such thing
    decreases o.AMFO
   requires o.Ready()
    requires pivot.Ready()
  //  ensures rv == (set oo <- o.owner, ooo <- uncollectAllPivotlyOutside(oo, pivot) :: ooo)   //wont prove
     ensures rv ==  {o} + uFE_body(o,pivot)

    {
      if (true)
          then  {o} + uFE_body(o,pivot)
          else  {o} + uFE_body(o,pivot)
    }

function uncollectFcckingEverything0rig(o : Object, pivot : Object) : (rv : set<Object>)
  // all o's transitive owners recursively.  so just collectAllOwners or some such thing
    decreases o.AMFO
   requires o.Ready()
    requires pivot.Ready()
     ensures rv == {o} + (set oo <- o.owner, ooo <- uncollectAllPivotlyOutside(oo, pivot) :: ooo)   //wont prove

    {

      if (true)
          then  {o} + (set oo <- o.owner, ooo <- uncollectAllPivotlyOutside(oo, pivot) :: ooo)
          else  {o} + (set oo <- o.owner, ooo <- uncollectAllPivotlyOutside(oo, pivot) :: ooo)
    }


lemma LAMME_uncollectFcckingEverything(o : Object, pivot : Object, rv : set<Object>)
  // all o's transitive owners recursively.  so just collectAllOwners or some such thing
    decreases o.AMFO
   requires o.Ready()
   requires rv == uncollectAllPivotlyOutside(o, pivot)
    ensures rv == {o} + (set oo <- o.owner, ooo <- uncollectAllPivotlyOutside(oo, pivot) :: ooo)

    {
      if (true)
         { assert rv == {o} + (set oo <- o.owner, ooo <- uncollectAllPivotlyOutside(oo, pivot) :: ooo); }
      else
         { assert rv == {o} + (set oo <- o.owner, ooo <- uncollectAllPivotlyOutside(oo, pivot) :: ooo); }
    }




function uncollectAllPivotlyOutside2(o : Object, pivot : Object) : (rv : set<Object>)
  // all o's transitive owners that are the pivot or outside pivot
  // recursive, NON-shortcutting analogue of allInside - collectAllPivotlyOutside
  decreases o.AMFO
   requires o.Ready()
    ensures pivotlyOutside(o,pivot) ==> (o in rv)
    ensures forall oo <- o.owner :: (uncollectAllPivotlyOutside(oo, pivot) <= rv)
    ensures pivotlyOutside(o,pivot) ==> (rv <= {o} + (set oo <- o.owner, ooo <- uncollectAllPivotlyOutside(oo, pivot) :: ooo))
    ensures pivotlyOutside(o,pivot) ==> (rv >= {o} + (set oo <- o.owner, ooo <- uncollectAllPivotlyOutside(oo, pivot) :: ooo))
    ensures pivotlyOutside(o,pivot) ==> (rv == {o} + (set oo <- o.owner, ooo <- uncollectAllPivotlyOutside(oo, pivot) :: ooo))
    {
      if (pivotlyOutside(o,pivot))
          then  {o} + (set oo <- o.owner, ooo <- uncollectAllPivotlyOutside(oo, pivot) :: ooo)
          else        (set oo <- o.owner, ooo <- uncollectAllPivotlyOutside(oo, pivot) :: ooo)
    }

lemma LEMMA_uncollectAllPivotlyOutside2(o : Object, pivot : Object)
  // all o's transitive owners that are strictly inside pivot
  // recursive, NON-shortcutting analogue of allInside - collectAllPivotlyOutside
    decreases o.AMFO
     requires o.Ready()
      ensures uncollectAllPivotlyOutside(o,pivot) == uncollectAllPivotlyOutside2(o,pivot)
{}


lemma LEMMA_collectAllPivotlyOutside(o : Object, pivot : Object)
  // all o's transitive owners that are strictly inside pivot
  // recursive, NON-shortcutting analogue of allInside - collectAllPivotlyOutside
    decreases o.AMFO
     requires o.Ready()
      ensures   collectAllPivotlyOutside(o,pivot) <= o.AMFO
      ensures uncollectAllPivotlyOutside(o,pivot) <= o.AMFO
      ensures forall x <-   collectAllPivotlyOutside(o,pivot) :: pivotlyOutside(x,pivot)
      ensures forall x <- uncollectAllPivotlyOutside(o,pivot) :: pivotlyOutside(x,pivot)
{}


//
//  lemma LEMMA_collectAllPivotlyOutside_FUCKEFD(o : Object, pivot : Object, cApO : Owner, subA : Owner)
//   // all o's transitive owners that are strictly inside pivot
//   // recursive, NON-shortcutting analogue of allInside - collectAllPivotlyOutside
//     decreases o.AMFO
//      requires o.Ready()
//      requires cApO == collectAllPivotlyOutside(o,pivot)
//      requires subA == set x <- o.AMFO | pivotlyOutside(x,pivot) :: x
//
//       ensures cApO <= o.AMFO
//       ensures subA <= o.AMFO
//
//       ensures forall x <- cApO :: x in subA
// //      ensures forall x <- subA :: x in cApO //ERR
//
//       ensures cApO <= subA
// //      ensures cApO >= subA  //ERR
// //      ensures cApO == subA //ERR
//
// {
//    LEMMA_collectAllPivotlyOutside(o,pivot);
//    forall x <- o.AMFO ensures (true) {
//       if pivotlyOutside(x,pivot) {
//           assert x in subA;
//          assert x in cApO;
//       }
//    }
// argh_LEMMA0(o);
//       forall x <- argh(o) ensures (true) {
//       if pivotlyOutside(x,pivot) {
//          assert x in subA;
//         assert x in cApO;
//       }
//    }
// }




//
//
// lemma LEMMA_uncollectAllPivotlyOutside2_AMFO(o : Object, pivot : Object)
//   // all o's transitive owners that are strictly inside pivot
//   // recursive, NON-shortcutting analogue of allInside - collectAllPivotlyOutside
//     decreases o.AMFO
//      requires o.Ready()
//      requires pivot.Ready()
//      requires pivotlyOutside(o,pivot)
//       ensures    collectAllPivotlyOutside(o,pivot) == o.AMFO
//    // ensures uncollectAllPivotlyOutside2(o,pivot) == o.AMFO
// {
//    if (o.owner == {})
//       {
//          assert o.AMFO == {o};
//          assert uncollectAllPivotlyOutside2(o,pivot) == {o};
//          assert uncollectAllPivotlyOutside2(o,pivot) == o.AMFO;
//          return;
//       }
//
//
//    OWNER_OUTSIDE_ALWAYS_OUTSIDE(o,pivot);
//    forall oo <- o.owner ensures (uncollectAllPivotlyOutside2(oo,pivot) == oo.AMFO) //by
//     {
//       assert pivotlyOutside(oo,pivot);
//       LEMMA_uncollectAllPivotlyOutside2_AMFO(oo, pivot);
//     }
//    assert forall oo <- o.owner :: uncollectAllPivotlyOutside2(oo,pivot) == oo.AMFO;
//
//    var rv := uncollectAllPivotlyOutside2(o,pivot);
//    assert pivotlyOutside(o,pivot);
// }
//


lemma OWNER_OUTSIDE_ALWAYS_OUTSIDE(o : Object, pivot : Object)
  decreases o.AMFO
   requires o.Ready()
   requires pivot.Ready()
    ensures (o == pivot)     ==> forall oo <- o.owner :: outside(oo,pivot)
    ensures outside(o,pivot) ==> forall oo <- o.owner :: outside(oo,pivot)
    ensures pivotlyOutside(o,pivot) ==> forall oo <- o.owner :: outside(oo,pivot)
    ensures pivotlyOutside(o,pivot) ==> forall oo <- o.AMFX  :: outside(oo,pivot)
{}


//======================================================================
//======================================================================
//======================================================================



function argh(o : Object) : (rv : Owner)
//clean recursive alter alternative definition of AMFO (recAmfo?) // recAllOwners
  decreases o.AMFO
  // requires o.Ready()
 { assume o.Ready();
   {o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo) }

function amfoStrictlyInside(o : Object, pivot : Object) : Owner
  decreases o.AMFO
   requires o.Ready()
 { allStrictlyInside(o.AMFO, pivot) }

function arghStrictlyInside(o : Object, pivot : Object) : Owner
  decreases o.AMFO
   requires o.Ready()
 { allStrictlyInside(argh(o), pivot) }


function amfoPivotlyOutside(o : Object, pivot : Object) : Owner
  decreases o.AMFO
   requires o.Ready()
 { allPivotlyOutside(o.AMFO, pivot) }

function arghPivotlyOutside(o : Object, pivot : Object) : Owner
  decreases o.AMFO
   requires o.Ready()
 { allPivotlyOutside(argh(o), pivot) }

































opaque function A(o : Object, pivot : Object) : Owner { {} }
opaque function B(o : Object, pivot : Object) : Owner { {o} }




lemma SETS_A_B(o : Object, pivot : Object)
  decreases o.AMFO
   requires forall oo <- o.owner :: A(oo,pivot) == B(oo,pivot)
    ensures forall oo <- o.owner :: (set ooo <- A(oo,pivot) :: ooo) == (set ooo <- B(oo,pivot) :: ooo)
   // ensures (set oo <- o.owner, ooo <- (set x <- uncollectFcckingEverything(oo,pivot)) :: ooo) == (set oo <- o.owner, ooo <- argh(oo) :: ooo)
    ensures (set oo <- o.owner, ooo <- A(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- B(oo,pivot) :: ooo)
 {}




lemma UFE_ARGH_SETS(o : Object, pivot : Object)
  decreases o.AMFO
   requires o.Ready()
   requires forall oo <- o.owner :: uncollectFcckingEverything(oo,pivot) == argh(oo)
    ensures forall oo <- o.owner :: (set ooo <- uncollectFcckingEverything(oo,pivot) :: ooo) == (set ooo <- argh(oo) :: ooo)
   // ensures (set oo <- o.owner, ooo <- (set x <- uncollectFcckingEverything(oo,pivot)) :: ooo) == (set oo <- o.owner, ooo <- argh(oo) :: ooo)
    ensures (set oo <- o.owner, ooo <- uncollectFcckingEverything(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- argh(oo) :: ooo)
 {}


lemma UFE_ARGH_SETS2(o : Object, pivot : Object, lset : Owner, rset : Owner)
  decreases o.AMFO
   requires o.Ready()
   requires forall oo <- o.owner :: uncollectFcckingEverything(oo,pivot) == argh(oo)
   requires lset == (set oo <- o.owner, ooo <- uncollectFcckingEverything(oo,pivot) :: ooo)
   requires rset == (set oo <- o.owner, ooo <- argh(oo) :: ooo)
    ensures forall oo <- o.owner :: (set ooo <- uncollectFcckingEverything(oo,pivot) :: ooo) == (set ooo <- argh(oo) :: ooo)
   // ensures (set oo <- o.owner, ooo <- (set x <- uncollectFcckingEverything(oo,pivot)) :: ooo) == (set oo <- o.owner, ooo <- argh(oo) :: ooo)
    ensures (set oo <- o.owner, ooo <- uncollectFcckingEverything(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- argh(oo) :: ooo)
    ensures rset == lset
 {}

// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

lemma UFE_ARGH(o : Object, pivot : Object, apo : Owner, asi : Owner)
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires apo == uncollectFcckingEverything(o, pivot) //arghPivotlyOutside(o, pivot)
    requires asi == argh(o)
     ensures apo == asi
 {
  //  if (o.owner == {})
  //   {
  //     assert apo == {o};
  //     assert asi == {o};
  //     assert apo == asi;
  //     return;
  //   }

  forall oo <- o.owner ensures (uncollectFcckingEverything(oo,pivot) == argh(oo)) //by
   {
      UFE_ARGH(oo,pivot,uncollectFcckingEverything(oo,pivot),argh(oo));
   }
  //  var lset := (set oo <- o.owner, ooo <- uncollectFcckingEverything(oo,pivot) :: ooo);
  //  var rset := (set oo <- o.owner, ooo <- argh(oo) :: ooo);
  //  UFE_ARGH_SETS2(o,pivot,lset,rset);
  //  assert lset == rset;
  //  assert (set oo <- o.owner, ooo <- uncollectFcckingEverything(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- argh(oo) :: ooo);
  //  assert argh(o) ==  {o} + rset;
  //  assert uncollectFcckingEverything(o,pivot) ==  ({o} + lset);
  //  assert ({o} + lset) == ({o} + rset);
 }


// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

lemma uncollectAllStrictlyInside_LEMMA0(o : Object, pivot : Object, skip : Owner, unskip : Owner)
  //unskip equals skip
  decreases o.AMFO
   requires o.Ready()
   requires skip   == collectAllStrictlyInside(o, pivot)
   requires unskip == uncollectAllStrictlyInside(o, pivot)
    ensures unskip == skip
   {
      if (not(strictlyInside(o,pivot)))
        {
         assert   collectAllStrictlyInside(o, pivot) == {};
         uncollectAllStrictlyInside_LEMMA1(o,pivot);
         assert uncollectAllStrictlyInside(o, pivot) == {};
         assert unskip == skip;
         return;
        }

      assert  strictlyInside(o,pivot);

      assert o in skip;
      assert o in unskip;

      assert o.Ready(); assert AllReady(o.owner);
      forall oo <- o.owner
        ensures (uncollectAllStrictlyInside(oo, pivot) == collectAllStrictlyInside(oo, pivot)) {
            assert o.AMFO decreases to oo.AMFO;
            var oo_skip   :=   collectAllStrictlyInside(oo, pivot);
            var oo_unskip := uncollectAllStrictlyInside(oo, pivot);
            uncollectAllStrictlyInside_LEMMA0(oo, pivot, oo_skip, oo_unskip);
            assert oo_skip == oo_unskip;
      }
   }


lemma uncollectAllStrictlyInside_LEMMA1(o : Object, pivot : Object)
  //unskip outside pivot is always empty --- hmm??? (1i below is better...)
  decreases o.AMFO
   requires o.Ready()
   requires (not(strictlyInside(o,pivot)))
    ensures uncollectAllStrictlyInside(o, pivot) == {}
    ensures forall r <- uncollectAllStrictlyInside(o, pivot) :: strictlyInside(o, pivot)
   {
      forall oo <- o.owner
        ensures (uncollectAllStrictlyInside(o, pivot) == {})
        {
         argh_LEMMA2(oo,pivot);
         assert (not(strictlyInside(oo,pivot)));
         uncollectAllStrictlyInside_LEMMA1(oo,pivot);
         assert uncollectAllStrictlyInside(oo, pivot) == {};
        }

   }


lemma uncollectAllStrictlyInside_LEMMA1i(o : Object, pivot : Object)
  //unskip results are always strictlyInsice
  decreases o.AMFO
   requires o.Ready()
   ensures forall r <- uncollectAllStrictlyInside(o, pivot) :: strictlyInside(r, pivot)
   { }


lemma uncollectAllStrictlyInside_LEMMA1a(o : Object, pivot : Object)
  //unskip is always from transitive ownerhsip (AMFO/argh)
  decreases o.AMFO
   requires o.Ready()
    ensures forall r <- uncollectAllStrictlyInside(o, pivot) :: (r in argh(o))
    ensures uncollectAllStrictlyInside(o, pivot) <= argh(o)
   { }


lemma uncollectAllStrictlyInside_LEMMA1n(o : Object, pivot : Object)
  //if I'm inside I should be in unskipaAllInsidestrictlyInside
  decreases o.AMFO
   requires o.Ready()
    ensures forall x <- argh(o) | not(strictlyInside(x, pivot)) :: (x !in uncollectAllStrictlyInside(o, pivot))
   {
     uncollectAllStrictlyInside_LEMMA1i(o,pivot);
     assert forall r <- uncollectAllStrictlyInside(o, pivot) :: strictlyInside(r, pivot);
   }


lemma uncollectAllStrictlyInside_LEMMA1o(o : Object, pivot : Object, x : Object)
  //if x is inside x should be in unskipaAllInsidestrictlyInside
  decreases o.AMFO
   requires o.Ready()
   requires x in argh(o)
   requires strictlyInside(x,pivot)
    ensures x in uncollectAllStrictlyInside(o, pivot)
   {
      if (x == o) {assert x in uncollectAllStrictlyInside(o, pivot); return;}
      assert x != o;
      assert exists oo <- o.owner, xx <- argh(oo) :: x == xx;
      assert exists oo <- o.owner :: x in uncollectAllStrictlyInside(oo, pivot);
    }

lemma uncollectAllStrictlyInside_LEMMA1z(o : Object, pivot : Object)
  //if I'm inside I should be in uncollectAllStrictlyInside
  decreases o.AMFO
   requires o.Ready()
    ensures forall oo <- argh(o) | strictlyInside(oo,pivot) :: oo in uncollectAllStrictlyInside(o, pivot)

    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) <= uncollectAllStrictlyInside(o, pivot)
    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) >= uncollectAllStrictlyInside(o, pivot)
    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) == uncollectAllStrictlyInside(o, pivot)

    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) <= arghStrictlyInside(o, pivot)
    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) >= arghStrictlyInside(o, pivot)
    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) == arghStrictlyInside(o, pivot)

    ensures arghStrictlyInside(o,pivot) == uncollectAllStrictlyInside(o, pivot)
   {
    forall oo <- argh(o) | strictlyInside(oo,pivot) ensures ( oo in uncollectAllStrictlyInside(o, pivot) )  {
       assert o.Ready();
       assert oo in argh(o);
       assert strictlyInside(oo,pivot);
       uncollectAllStrictlyInside_LEMMA1o(o,pivot,oo);
       assert oo in uncollectAllStrictlyInside(o, pivot);
      }
    }


////////////////////////////////////////////////////////////////////////////////////
// Sat 5 September

lemma uncollectAllPivotlyOutside_LEMMA0(o : Object, pivot : Object, skip : Owner, unskip : Owner)
  //unskip equals skip
  decreases o.AMFO
   requires o.Ready()
   requires skip   == collectAllPivotlyOutside(o, pivot)
   requires unskip == uncollectAllPivotlyOutside(o, pivot)
    ensures unskip == skip
   {
      if (pivotlyOutside(o,pivot))
        {
         assert   collectAllPivotlyOutside(o, pivot) == o.AMFO;
         var uno := uncollectAllPivotlyOutside(o, pivot);
         uncollectAllPivotlyOutside_AMFO_LEMMA(o,pivot,uno);
         assert uno == o.AMFO;  //ERR
         assert unskip == skip;
         return;
        }

      assert  not(pivotlyOutside(o,pivot));

//       assert o !in skip;
//       assert o !in unskip;

      assert o.Ready(); assert AllReady(o.owner);
      forall oo <- o.owner
        ensures (uncollectAllPivotlyOutside(oo, pivot) == collectAllPivotlyOutside(oo, pivot)) {
            assert o.AMFO decreases to oo.AMFO;
            var oo_skip   :=   collectAllPivotlyOutside(oo, pivot);
            var oo_unskip := uncollectAllPivotlyOutside(oo, pivot);
            uncollectAllPivotlyOutside_LEMMA0(oo, pivot, oo_skip, oo_unskip);
            assert oo_skip == oo_unskip;
      }
   }



lemma uncollectAllPivotlyOutside_AMFO_LEMMA(o : Object, pivot : Object, unskip : Owner)
  decreases o.AMFO
   requires o.Ready()
   requires pivotlyOutside(o,pivot)
   requires unskip == uncollectAllPivotlyOutside(o, pivot)
    ensures unskip == o.AMFO
{
   assert o in unskip;
   forall oo <- o.owner ensures ( uncollectAllPivotlyOutside(oo, pivot) == oo.AMFO ) //by
    {
         var unoo := uncollectAllPivotlyOutside(oo, pivot);
         uncollectAllPivotlyOutside_AMFO_LEMMA(oo,pivot,unoo);
         assert unoo == oo.AMFO;
    }

}


lemma uncollectAllPivotlyOutside_LEMMA1o(o : Object, pivot : Object, x : Object)
  //if x is inside x should be in unskipaAllInsidepivotlyOutside
  decreases o.AMFO
   requires o.Ready()
   requires x in argh(o)
   requires pivotlyOutside(x,pivot)
    ensures x in uncollectAllPivotlyOutside(o, pivot)
   {
      if (x == o) {assert x in uncollectAllPivotlyOutside(o, pivot); return;}
      assert x != o;
      assert exists oo <- o.owner, xx <- argh(oo) :: x == xx;
      assert exists oo <- o.owner :: x in uncollectAllPivotlyOutside(oo, pivot);
    }

lemma uncollectAllPivotlyOutside_LEMMA1z(o : Object, pivot : Object)
  //if I'm inside I should be in uncollectAllPivotlyOutside
  decreases o.AMFO
   requires o.Ready()
    ensures forall oo <- argh(o) | pivotlyOutside(oo,pivot) :: oo in uncollectAllPivotlyOutside(o, pivot)

    ensures (set oo <- argh(o) | pivotlyOutside(oo,pivot)) <= uncollectAllPivotlyOutside(o, pivot)
    ensures (set oo <- argh(o) | pivotlyOutside(oo,pivot)) >= uncollectAllPivotlyOutside(o, pivot)
    ensures (set oo <- argh(o) | pivotlyOutside(oo,pivot)) == uncollectAllPivotlyOutside(o, pivot)

    ensures (set oo <- argh(o) | pivotlyOutside(oo,pivot)) <= arghPivotlyOutside(o, pivot)
    ensures (set oo <- argh(o) | pivotlyOutside(oo,pivot)) >= arghPivotlyOutside(o, pivot)
    ensures (set oo <- argh(o) | pivotlyOutside(oo,pivot)) == arghPivotlyOutside(o, pivot)

    ensures arghPivotlyOutside(o,pivot) == uncollectAllPivotlyOutside(o, pivot)
   {
    forall oo <- argh(o) | pivotlyOutside(oo,pivot) ensures ( oo in uncollectAllPivotlyOutside(o, pivot) )  {
       assert o.Ready();
       assert oo in argh(o);
       assert pivotlyOutside(oo,pivot);
       uncollectAllPivotlyOutside_LEMMA1o(o,pivot,oo);
       assert oo in uncollectAllPivotlyOutside(o, pivot);
      }
    }

/////////////////////////////////////////////////////////////////////////////////


lemma uncollectAllStrictlyInside_LEMMA2(o : Object, pivot : Object, arghIn : Owner, unskip : Owner)
  //unskip equals arghInside
  //rplaced with _LEMMA1*
  decreases o.AMFO
   requires o.Ready()
   requires pivot.Ready()
   requires arghIn == arghStrictlyInside(o, pivot)
   requires unskip == uncollectAllStrictlyInside(o, pivot)

    ensures unskip == arghIn
   {
     uncollectAllStrictlyInside_LEMMA1z(o,pivot);
   }


lemma uncollectAllStrictlyInside_LEMMA3(o : Object, pivot : Object)
 //given uncollectAllStrictlyInside owners == arghStrictlyInside owners
 //then  set of unskips is set of arghStrictlyInside
//not really used (much)
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: uncollectAllStrictlyInside(oo, pivot) == arghStrictlyInside(oo, pivot)

   // these two doesn't work
   //   ensures forall oo <- o.owner :: ((set ooo <- uncollectAllStrictlyInside(oo, pivot) :: ooo) == (set ooo <- arghStrictlyInside(oo, pivot) :: ooo))
   //   ensures (set oo <- o.owner, ooo <- uncollectAllStrictlyInside(oo, pivot) :: ooo) == (set oo <- o.owner, ooo <- arghStrictlyInside(oo, pivot) :: ooo)

     ensures forall oo <- o.owner :: (set ooo <- uncollectAllStrictlyInside(oo,pivot) :: ooo) == (set ooo <- arghStrictlyInside(oo,pivot) :: ooo)
     ensures (set oo <- o.owner, ooo <- (set x <- uncollectAllStrictlyInside(oo,pivot)) :: ooo) == (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo)
     ensures (set oo <- o.owner, ooo <- uncollectAllStrictlyInside(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo)

{
   forall oo <- o.owner ensures ((set ooo <- uncollectAllStrictlyInside(oo, pivot) :: ooo) == (set ooo <- arghStrictlyInside(oo, pivot) :: ooo))
      {
         assert uncollectAllStrictlyInside(oo, pivot) == arghStrictlyInside(oo, pivot);
      }
   assert forall oo <- o.owner ::  ((set ooo <- uncollectAllStrictlyInside(oo, pivot) :: ooo) == (set ooo <- arghStrictlyInside(oo, pivot) :: ooo));
}



lemma uncollectAllStrictlyInside_LEMMA4(o : Object, pivot : Object, left : Owner, rite : Owner)  //UNUSED?
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    // requires strictlyInside(o,pivot)
    requires left == (set oo <- o.owner, ooo <- uncollectAllStrictlyInside(oo,pivot) :: ooo)
    requires rite == (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo)
    requires left == rite
     ensures {o} + left == {o} + rite
{
  SetPlus1(o,left,rite);
}


// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //


lemma arghStrictlyInside_LEMMA0(o : Object, pivot : Object)
 // amfoStrictlyInside == arghStrictlyInside == allStrictlyInside
  decreases o.AMFO
   requires o.Ready()
   requires pivot.Ready()
    ensures arghStrictlyInside(o,pivot) == allStrictlyInside(argh(o),pivot)
    ensures amfoStrictlyInside(o,pivot) == allStrictlyInside(o.AMFO,pivot)
    ensures allStrictlyInside(argh(o),pivot) == allStrictlyInside(o.AMFO,pivot)
    ensures arghStrictlyInside(o,pivot) == amfoStrictlyInside(o,pivot)
{
      argh_LEMMA0(o);
      assert argh(o) == o.AMFO;
}


lemma arghStrictlyInside_LEMMA1(o : Object, pivot : Object)
    //arghStrictlyInside outside pivot is always empty
  decreases o.AMFO
   requires o.Ready()
   requires (not(strictlyInside(o,pivot)))
    ensures arghStrictlyInside(o, pivot) == {}
   {
      forall oo <- o.owner
        ensures (arghStrictlyInside(o, pivot) == {})
        {
         argh_LEMMA2(oo,pivot);
         assert (not(strictlyInside(oo,pivot)));
         arghStrictlyInside_LEMMA1(oo,pivot);
         assert arghStrictlyInside(o, pivot) == {};
        }

   }


lemma arghStrictlyInside_LEMMA1b(o : Object, pivot : Object)   //WORKS
 //lifts asI==sAi to sets
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: arghStrictlyInside(oo,pivot) == collectAllStrictlyInside(oo,pivot)
     ensures forall oo <- o.owner :: (set ooo <- arghStrictlyInside(oo,pivot) :: ooo) == (set ooo <- collectAllStrictlyInside(oo,pivot) :: ooo)
     ensures (set oo <- o.owner, ooo <- (set x <- arghStrictlyInside(oo,pivot)) :: ooo) == (set oo <- o.owner, ooo <- collectAllStrictlyInside(oo,pivot) :: ooo)
     ensures (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- collectAllStrictlyInside(oo,pivot) :: ooo)
{
   // forall oo <- o.owner ensures (set ooo <- arghStrictlyInside(oo,pivot) :: ooo) == (set ooo <- collectAllStrictlyInside(oo,pivot) :: ooo)
   //    {
   //       assert arghStrictlyInside(oo,pivot) == collectAllStrictlyInside(oo,pivot);
   //    }
}

// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

lemma XXXcollectAllStrictlyInside_LEMMA1a(o : Object, pivot : Object)   ///DOESNT WORK - calls UNPROVED subLEMMERS
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
//    requires strictlyInside(o,pivot)
//     ensures forall oo <- o.owner :: allStrictlyInside(oo.AMFO,pivot) == collectAllStrictlyInside(oo,pivot)
     ensures allStrictlyInside(o.AMFO,pivot) == collectAllStrictlyInside(o,pivot)
{
      if (not(strictlyInside(o,pivot)))
        {
            assert collectAllStrictlyInside(o,pivot) == {};
            o.ExtraReady();
            assert allStrictlyInside(o.AMFO,pivot) == {};
            assert allStrictlyInside(o.AMFO,pivot) == collectAllStrictlyInside(o,pivot);
            return;
        }

      assert strictlyInside(o,pivot);

      if (o.owner == {})
       {
          assert allStrictlyInside(o.AMFO,pivot) == collectAllStrictlyInside(o,pivot);
          return;
       }

       assert o.owner > {};

       forall oo <- o.owner
         ensures allStrictlyInside(oo.AMFO,pivot) == collectAllStrictlyInside(oo,pivot)
         {
            XXXcollectAllStrictlyInside_LEMMA1a(oo,pivot);
            assert allStrictlyInside(oo.AMFO,pivot) == collectAllStrictlyInside(oo,pivot);
         }

       var aSI := (set oo <- o.owner, x <- allStrictlyInside(oo.AMFO,pivot) :: x);
       var sAI := (set oo <- o.owner, x <- collectAllStrictlyInside(oo,pivot) :: x);

       assert forall oo <- o.owner :: allStrictlyInside(oo.AMFO,pivot) == collectAllStrictlyInside(oo,pivot);
       collectAllStrictlyInside_LEMMA1b(o,pivot);
       assert (set oo <- o.owner, x <- allStrictlyInside(oo.AMFO,pivot) :: x) == (set oo <- o.owner, x <- collectAllStrictlyInside(oo,pivot) :: x);
       collectAllStrictlyInside_LEMMA1c(o, pivot, aSI, sAI);  //COS THIS DOESNT WORK

       assert {o} + aSI == {o} + sAI;

       assert collectAllStrictlyInside(o,pivot) == {o} + (set oo <- o.owner, ooo <- collectAllStrictlyInside(oo,pivot) :: ooo);
       assert collectAllStrictlyInside(o,pivot) == {o} + sAI;
       assert allStrictlyInside(o.AMFO,pivot) == {o} + aSI;
       assert allStrictlyInside(o.AMFO,pivot) == collectAllStrictlyInside(o,pivot);
}


lemma collectAllStrictlyInside_LEMMA1b(o : Object, pivot : Object)   //WORKS
 //lifts asI==sAi to sets
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: allStrictlyInside(oo.AMFO,pivot) == collectAllStrictlyInside(oo,pivot)
     ensures forall oo <- o.owner :: (set ooo <- allStrictlyInside(oo.AMFO,pivot) :: ooo) == (set ooo <- collectAllStrictlyInside(oo,pivot) :: ooo)
     ensures (set oo <- o.owner, ooo <- (set x <- allStrictlyInside(oo.AMFO,pivot)) :: ooo) == (set oo <- o.owner, ooo <- collectAllStrictlyInside(oo,pivot) :: ooo)
     ensures (set oo <- o.owner, ooo <- allStrictlyInside(oo.AMFO,pivot) :: ooo) == (set oo <- o.owner, ooo <- collectAllStrictlyInside(oo,pivot) :: ooo)
{
   forall oo <- o.owner ensures (set ooo <- allStrictlyInside(oo.AMFO,pivot) :: ooo) == (set ooo <- collectAllStrictlyInside(oo,pivot) :: ooo)
      {
         assert allStrictlyInside(oo.AMFO,pivot) == collectAllStrictlyInside(oo,pivot);
      }
}

lemma {:verify false} collectAllStrictlyInside_LEMMA1c(o : Object, pivot : Object, aSI : Owner, sAI : Owner)   //DOESNT WORK
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: allStrictlyInside(oo.AMFO,pivot) == collectAllStrictlyInside(oo,pivot)
    requires aSI == (set oo <- o.owner, ooo <- allStrictlyInside(oo.AMFO,pivot) :: ooo)
    requires AllReady(aSI)
    requires sAI == (set oo <- o.owner, ooo <- collectAllStrictlyInside(oo,pivot) :: ooo)
    requires AllReady(sAI)
    requires aSI == sAI
     ensures {o} + aSI == {o} + sAI
     ensures allStrictlyInside(o.AMFO,pivot) == {o} + aSI    //ERR
     ensures collectAllStrictlyInside(o,pivot) ==
         if (not(strictlyInside(o,pivot))) then ({}) else ({o} + sAI)
{
//assert allStrictlyInside(o.AMFO,pivot) == {};A

//(set o <- soup | strictlyInside(o,whole) )
}



lemma {:verify false} collectAllStrictlyInside_LEMMA1d(o : Object, pivot : Object, aSI : Owner, sAI : Owner)  //DOESNT WORK
  /// version of collectAllStrictlyInside_LEMMA1c - but using arghStrictlyInside
  /// WHAT NEEDS TO HAPPEN is to invert the polarity control flow?
  ///  from
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: arghStrictlyInside(o,pivot) == collectAllStrictlyInside(oo,pivot)
    requires aSI == (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo)
    requires sAI == (set oo <- o.owner, ooo <- collectAllStrictlyInside(oo,pivot) :: ooo)
    requires aSI == sAI

     ensures {o} + aSI == {o} + sAI
   //   ensures arghStrictlyInside(o,pivot) ==   // {o} + aSI  //xERR
   //       if (not(strictlyInside(o,pivot))) then ({}) else ({o} + aSI)
     ensures arghStrictlyInside(o,pivot) ==   // {o} + aSI  //ERR
         if (not(strictlyInside(o,pivot))) then ({}) else ({o} + aSI)

     ensures collectAllStrictlyInside(o,pivot) ==
         if (not(strictlyInside(o,pivot))) then ({}) else ({o} + sAI)
{
   //can the lift-forall-to-set lemma help here?


   //make skipall inside just iterate of thre whole fucking AMDO
   //and pick each individsual ;node
   //rqather than stopping "early"?????
   //  **uncollectAllStrictlyInside** (or recAllInside)
}

// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //


lemma argh_LEMMA0(o : Object)
//establishes o.AMFO == argh(o)
  decreases o.AMFO
   requires o.Ready()
    ensures o.AMFO == argh(o)
    ensures forall oo <- o.owner :: argh(oo) == oo.AMFO
{
   if (o.owner == {}) {return;}

   forall oo <- o.owner ensures (true)
   {
      argh_LEMMA0(oo);
      assert argh(oo) == oo.AMFO;
   }
}

lemma argh_LEMMA1(o : Object)
 //deconstructs AMFO to iteration over *owners*
  decreases o.AMFO
   requires o.Ready()
    ensures o.AMFO == ({o} + (set oo <- o.owner, ooo <- oo.AMFO :: ooo))
{}

lemma argh_LEMMA2(o : Object, pivot : Object)   //ONCE_OUTSIDE_ALL_OUTSIDE
//once owner is outside pivot, always outside pivot
  decreases o.AMFO
   requires o.Ready()
   requires not(strictlyInside(o,pivot))
    ensures forall oo <- o.owner :: not(strictlyInside(oo,pivot))
    ensures forall oo <- o.AMFO  :: not(strictlyInside(oo,pivot))
{}

lemma argh_LEMMA3(o : Object)
 //result of argh are ready
  decreases o.AMFO
   requires o.Ready()
    ensures AllReady( argh(o) )
{
   argh_LEMMA0(o);
}

lemma argh_LEMMA4(o : Object)
 //deconstructs AMFO to iteration over *owners*
  decreases o.AMFO
   requires o.Ready()
    ensures argh(o) == ({o} + (set oo <- o.owner, ooo <- oo.AMFO :: ooo))
{
     argh_LEMMA0(o);
}

lemma argh_LEMMA9(o : Object, pivot : Object)
 //close to being tautologous but given owners argh(oo)==oo.AMFO, lifts that to forall oo <- o.owners
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: argh(oo) == oo.AMFO

   // these two doesn't work
   //   ensures forall oo <- o.owner :: ((set ooo <- uncollectAllStrictlyInside(oo, pivot) :: ooo) == (set ooo <- arghStrictlyInside(oo, pivot) :: ooo))
   //   ensures (set oo <- o.owner, ooo <- uncollectAllStrictlyInside(oo, pivot) :: ooo) == (set oo <- o.owner, ooo <- arghStrictlyInside(oo, pivot) :: ooo)

     ensures forall oo <- o.owner :: (set ooo <- argh(oo) :: ooo) == (set ooo <- oo.AMFO :: ooo)
     ensures (set oo <- o.owner, ooo <- (set x <- argh(oo)) :: ooo) == (set oo <- o.owner, ooo <- oo.AMFO :: ooo)
     ensures (set oo <- o.owner, ooo <- argh(oo) :: ooo) == (set oo <- o.owner, ooo <- oo.AMFO :: ooo)
     ensures ({o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo)) == ({o} + (set oo <- o.owner, ooo <- oo.AMFO :: ooo))
     ensures argh(o) == ({o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo))
     ensures argh(o) == ({o} + (set oo <- o.owner, ooo <- oo.AMFO  :: ooo))
{
  forall oo <- o.owner ensures ((set ooo <- argh(oo) :: ooo) == (set ooo <- oo.AMFO :: ooo))
      {
         assert argh(oo) == oo.AMFO;
      }

   assert forall oo <- o.owner ::  ((set ooo <- argh(oo) :: ooo) == (set ooo <- oo.AMFO :: ooo));
}


lemma argh_LEMMA13(o : Object, pivot : Object)
    requires o.Ready()
    requires pivot.Ready()
     ensures collectAllStrictlyInside(o,pivot) == amfoStrictlyInside(o,pivot)
{
   uncollectAllStrictlyInside_LEMMA0(o,pivot, collectAllStrictlyInside(o, pivot), uncollectAllStrictlyInside(o, pivot));
    assert collectAllStrictlyInside(o,pivot) == uncollectAllStrictlyInside(o,pivot);
   uncollectAllStrictlyInside_LEMMA1z(o, pivot);
    assert uncollectAllStrictlyInside(o, pivot) == arghStrictlyInside(o,pivot);
   arghStrictlyInside_LEMMA0(o,pivot);
    assert arghStrictlyInside(o,pivot) == amfoStrictlyInside(o,pivot);
}


lemma {:verify false} argh_LEMMA13orig(o : Object, pivot : Object)  //doesn't work without assume
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
     ensures arghStrictlyInside(o,pivot) == collectAllStrictlyInside(o,pivot)//ERR
{
    if (not(strictlyInside(o,pivot)))
    {
        argh_LEMMA13a(o,pivot);
        assert arghStrictlyInside(o,pivot) == {};
        assert arghStrictlyInside(o,pivot) == collectAllStrictlyInside(o,pivot) == {};
        return;
        }
    assert strictlyInside(o,pivot);

    if (o.owner == {})
     {
        assert collectAllStrictlyInside(o,pivot) == {o};
        assert arghStrictlyInside(o,pivot) == {o};
        assert arghStrictlyInside(o,pivot) == collectAllStrictlyInside(o,pivot) == {o};
        return;
     }
     assert o.owner > {};
     forall oo <- o.owner
       ensures arghStrictlyInside(oo,pivot) == collectAllStrictlyInside(oo,pivot)
       {
         argh_LEMMA13(oo,pivot);
         assert arghStrictlyInside(oo,pivot) == collectAllStrictlyInside(oo,pivot);
       }

     arghStrictlyInside_LEMMA1b(o,pivot);

     assert  (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo) ==
             (set oo <- o.owner, ooo <- collectAllStrictlyInside(oo,pivot) :: ooo);

    //  assert arghStrictlyInside(o,pivot) == {o} + (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo);

      assert collectAllStrictlyInside(o,pivot) == {o} + (set oo <- o.owner, ooo <- collectAllStrictlyInside(oo,pivot) :: ooo);

// assume  arghStrictlyInside(o,pivot) == collectAllStrictlyInside(o,pivot);
}


lemma argh_LEMMA13a(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires not(strictlyInside(o,pivot))
     ensures arghStrictlyInside(o,pivot) == {}
{
   assert forall x <- o.AMFO :: not(strictlyInside(x,pivot));
   assert  arghStrictlyInside(o,pivot) == {};
}

lemma argh_LEMMA13c(o : Object, a : Owner, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires a == argh(o)
    requires AllReady(a)
    requires pivot.Ready()
    requires (strictlyInside(o,pivot))
    requires o.owner > {}
     ensures allStrictlyInside(a,pivot) == (set o : Object <- a | strictlyInside(o,pivot))
     {
         argh_LEMMA3(o);
         argh_LEMMA13d(a,pivot);

         assert allStrictlyInside(a,pivot) == (set o : Object <- a | strictlyInside(o,pivot));
     }

lemma argh_LEMMA13d(oo : Owner, pivot : Object)
    requires AllReady(oo)
    requires pivot.Ready()
     ensures allStrictlyInside(oo,pivot) ==  (set o : Object <- oo | strictlyInside(o,pivot) )
   {}
