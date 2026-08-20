include "Ownership.dfy"

//pretty sure the main point of this entire file
//is to prove that skipAllInside(o,pivot) == arghStrictlyInside)(o,pivot)
//i.e,.                                   == allStrictlyInside(argh(o),pivot)
//
// skip all inside is recursive & terminates early;
//  allStrictlyInside is iteraative sugar for a set comprehension.
//
//   assert (set x <- next.AMFO | strictlyInside(x,m.o)) == skipAllInside(next,m.o);
//   assert (set x <- cext.AMFO | strictlyInside(x,m.c)) == skipAllInside(cext,m.c);


function skipAllInside(o : Object, pivot : Object) : (rv : set<Object>)
  // all o's transitive owners strictly inside pivot
  // recursive, shortcutting analogue of allInside
  decreases o.AMFO
   requires o.Ready()
    {
      if (not(strictlyInside(o,pivot))) then ({})
          else  {o} + (set oo <- o.owner, ooo <- skipAllInside(oo, pivot) :: ooo)
    }

function unskipAllInside(o : Object, pivot : Object) : (rv : set<Object>)
  // all o's transitive owners strictly inside pivot
  // recursive, NON-shortcutting analogue of allInside - skipAllInside
    decreases o.AMFO
   requires o.Ready()
    {
      if (not(strictlyInside(o,pivot)))
          then        (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo)
          else  {o} + (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo)
    }


lemma {:timeLimit 3} unskipAllInside_LEMMA0(o : Object, pivot : Object, skip : Owner, unskip : Owner)
  //unskip equals skip
  decreases o.AMFO
   requires o.Ready()
   requires skip   == skipAllInside(o, pivot)
   requires unskip == unskipAllInside(o, pivot)
    ensures unskip == skip
   {
      if (not(strictlyInside(o,pivot)))
        {
         assert   skipAllInside(o, pivot) == {};
         unskipAllInside_LEMMA1(o,pivot);
         assert unskipAllInside(o, pivot) == {};
         assert unskip == skip;
         return;
        }

      assert  strictlyInside(o,pivot);

      assert o in skip;
      assert o in unskip;

      assert o.Ready(); assert AllReady(o.owner);
      forall oo <- o.owner
        ensures (unskipAllInside(oo, pivot) == skipAllInside(oo, pivot)) {
            assert o.AMFO decreases to oo.AMFO;
            var oo_skip   :=   skipAllInside(oo, pivot);
            var oo_unskip := unskipAllInside(oo, pivot);
            unskipAllInside_LEMMA0(oo, pivot, oo_skip, oo_unskip);
            assert oo_skip == oo_unskip;
      }
   }







lemma unskipAllInside_LEMMA1(o : Object, pivot : Object)
  //unskip outside pivot is always empty
  decreases o.AMFO
   requires o.Ready()
   requires (not(strictlyInside(o,pivot)))
    ensures unskipAllInside(o, pivot) == {}
    ensures forall r <- unskipAllInside(o, pivot) :: strictlyInside(o, pivot)
   {
      forall oo <- o.owner
        ensures (unskipAllInside(o, pivot) == {})
        {
         argh_LEMMA2(oo,pivot);
         assert (not(strictlyInside(oo,pivot)));
         unskipAllInside_LEMMA1(oo,pivot);
         assert unskipAllInside(oo, pivot) == {};
        }

   }



lemma unskipAllInside_LEMMA1i(o : Object, pivot : Object)
  //unskip results are always strictlyInsice
  decreases o.AMFO
   requires o.Ready()
   ensures forall r <- unskipAllInside(o, pivot) :: strictlyInside(r, pivot)
   { }



lemma unskipAllInside_LEMMA1a(o : Object, pivot : Object)
  //unskip is always from tranwitive ownerhsip (AMFO/argh)
  decreases o.AMFO
   requires o.Ready()
    ensures forall r <- unskipAllInside(o, pivot) :: (r in argh(o))
    ensures unskipAllInside(o, pivot) <= argh(o)
   { }



lemma unskipAllInside_LEMMA1n(o : Object, pivot : Object)
  //if I'm inside I should be in unskipaAllInsidestrictlyInside
  decreases o.AMFO
   requires o.Ready()
    ensures forall x <- argh(o) | not(strictlyInside(x, pivot)) :: (x !in unskipAllInside(o, pivot))
   {
     unskipAllInside_LEMMA1i(o,pivot);
     assert forall r <- unskipAllInside(o, pivot) :: strictlyInside(r, pivot);

   }



lemma unskipAllInside_LEMMA1o(o : Object, pivot : Object, x : Object)
  //if I'm inside I should be in unskipaAllInsidestrictlyInside
  decreases o.AMFO
   requires o.Ready()
   requires x in argh(o)
   requires strictlyInside(x,pivot)
    ensures x in unskipAllInside(o, pivot)
   {
      if (x == o) {assert x in unskipAllInside(o, pivot); return;}
      assert x != o;

//      if (x in o.owner) {assert x in unskipAllInside(o, pivot); return;}

      assert exists oo <- o.owner, xx <- argh(oo) :: x == xx;
      assert exists oo <- o.owner :: x in unskipAllInside(oo, pivot);
    }



lemma unskipAllInside_LEMMA1z(o : Object, pivot : Object)
  //if I'm inside I should be in unskipaAllInsidestrictlyInside
  decreases o.AMFO
   requires o.Ready()
    ensures forall oo <- argh(o) | strictlyInside(oo,pivot) :: oo in unskipAllInside(o, pivot)

    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) <= unskipAllInside(o, pivot)
    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) >= unskipAllInside(o, pivot)
    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) == unskipAllInside(o, pivot)

    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) <= arghStrictlyInside(o, pivot)
    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) >= arghStrictlyInside(o, pivot)
    ensures (set oo <- argh(o) | strictlyInside(oo,pivot)) == arghStrictlyInside(o, pivot)

    ensures arghStrictlyInside(o,pivot) == unskipAllInside(o, pivot)
   {
    forall oo <- argh(o) | strictlyInside(oo,pivot) ensures ( oo in unskipAllInside(o, pivot) )  {   //oo in unskipAllInside(o, pivot)
       assert o.Ready();
       assert oo in argh(o);
       assert strictlyInside(oo,pivot);
       unskipAllInside_LEMMA1o(o,pivot,oo);
       assert oo in unskipAllInside(o, pivot);
      }

    }





//close up














lemma {:timeLimit 30} unskipAllInside_LEMMA2(o : Object, pivot : Object, arghIn : Owner, unskip : Owner)
  //unskip equals arghInside4\
  decreases o.AMFO
   requires o.Ready()
   requires pivot.Ready()
   requires arghIn == arghStrictlyInside(o, pivot)
   requires unskip == unskipAllInside(o, pivot)
    ensures forall oo <- o.owner :: unskipAllInside(oo, pivot) == arghStrictlyInside(oo, pivot)

    ensures unskip == arghIn
   {
      if (not(strictlyInside(o,pivot)))
        {
         arghStrictlyInside_LEMMA1(o,pivot);
         assert arghStrictlyInside(o, pivot) == {};
         unskipAllInside_LEMMA1(o,pivot);
         assert unskipAllInside(o, pivot) == {};
         assert unskip == arghIn;
         return;
        }

      assert strictlyInside(o,pivot);

      assert o in arghIn;
      assert o in unskip;

      assert o.Ready(); assert AllReady(o.owner);

      forall oo <- o.owner
        ensures (unskipAllInside(oo, pivot) == arghStrictlyInside(oo, pivot)) {
            assert o.AMFO decreases to oo.AMFO;
            var oo_arghIn := arghStrictlyInside(oo, pivot);
            var oo_unskip := unskipAllInside(oo, pivot);
            unskipAllInside_LEMMA2(oo, pivot, oo_arghIn, oo_unskip);
            assert oo_arghIn == oo_unskip;
        }

      assert forall oo <- o.owner :: unskipAllInside(oo, pivot) == arghStrictlyInside(oo, pivot);

      unskipAllInside_LEMMA3(o,pivot);

//       assert (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo) == (set oo <- o.owner, ooo <- arghStrictlyInside(oo, pivot) :: ooo);
//
//
//       assert unskip == {o} + (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo);
//
//     assert arghIn == arghStrictlyInside(o, pivot) == allStrictlyInside(argh(o),pivot) == (set x <- argh(o) | strictlyInside(x,pivot));
// argh_LEMMA0(o); cunty_LEMMA4(o,pivot);
//     assert arghIn == (set x <- argh(o) | strictlyInside(x,pivot))
//                   == (set x <- ({o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo))  | strictlyInside(x,pivot));


    assert (set x <- ({o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo))  | strictlyInside(x,pivot))
        == (set x <- {o} | strictlyInside(x,pivot)) + (set x <- (set oo <- o.owner, ooo <- argh(oo) :: ooo)  | strictlyInside(x,pivot)); //ERR

    assert (set x <- {o} | strictlyInside(x,pivot)) == {o}  by {  assert strictlyInside(o,pivot); } //ERR

    // assert (set x <- (set oo <- o.owner, ooo <- argh(oo) :: ooo)  | strictlyInside(x,pivot))
    //     ==           (set oo <- o.owner, ooo <- argh(oo) | strictlyInside(oo,pivot) :: ooo ) //ERR
    //     ==           (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo); //ERR


      forall oo <- o.owner
        ensures (unskipAllInside(oo, pivot) == arghStrictlyInside(oo, pivot)) {
            assert o.AMFO decreases to oo.AMFO;
            var oo_arghIn := arghStrictlyInside(oo, pivot);
            var oo_unskip := unskipAllInside(oo, pivot);
            unskipAllInside_LEMMA2(oo, pivot, oo_arghIn, oo_unskip);
            assert oo_arghIn == oo_unskip;
        }

assert        (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo) ==        (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo);

assert  {o} + (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo) == {o} +  (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo);

// assert  arghStrictlyInside(o,pivot) == unskipAllInside(o, pivot); //ERR

//
//       // assert arghIn == {o} + (set oo <- o.owner, ooo <- arghStrictlyInside(oo, pivot) :: ooo)  //ERR
//       //    by {  assert strictlyInside(o,pivot); }
//
      assert unskip == arghIn;

   }



lemma unskipAllInside_LEMMA3(o : Object, pivot : Object)   //WORKS
 //given unskipAllInside owners == arghStrictlyInside owners
 //then  set of unskips is set of arghStrictlyInside
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: unskipAllInside(oo, pivot) == arghStrictlyInside(oo, pivot)

   // these two doesn't work
   //   ensures forall oo <- o.owner :: ((set ooo <- unskipAllInside(oo, pivot) :: ooo) == (set ooo <- arghStrictlyInside(oo, pivot) :: ooo))
   //   ensures (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo) == (set oo <- o.owner, ooo <- arghStrictlyInside(oo, pivot) :: ooo)

     ensures forall oo <- o.owner :: (set ooo <- unskipAllInside(oo,pivot) :: ooo) == (set ooo <- arghStrictlyInside(oo,pivot) :: ooo)
     ensures (set oo <- o.owner, ooo <- (set x <- unskipAllInside(oo,pivot)) :: ooo) == (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo)
     ensures (set oo <- o.owner, ooo <- unskipAllInside(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo)

{
   forall oo <- o.owner ensures ((set ooo <- unskipAllInside(oo, pivot) :: ooo) == (set ooo <- arghStrictlyInside(oo, pivot) :: ooo))
      {
         assert unskipAllInside(oo, pivot) == arghStrictlyInside(oo, pivot);
      }

   assert forall oo <- o.owner ::  ((set ooo <- unskipAllInside(oo, pivot) :: ooo) == (set ooo <- arghStrictlyInside(oo, pivot) :: ooo));
}

lemma setequals_LEMMA0(o : Object, left : Owner, right : Owner)
 requires left == right
  ensures {o} + left == {o} + right
{}



lemma unskipAllInside_LEMMA4(o : Object, pivot : Object, left : Owner, rite : Owner)
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    // requires strictlyInside(o,pivot)
    requires left == (set oo <- o.owner, ooo <- unskipAllInside(oo,pivot) :: ooo)
    requires rite == (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo)
    requires left == rite
     ensures {o} + left == {o} + rite
{
  setequals_LEMMA0(o,left,rite);
}


lemma cunty_LEMMA5(o : Object, pivot : Object, left : Owner)
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires strictlyInside(o,pivot)
    requires left == {o} + (set oo <- o.owner, ooo <- unskipAllInside(oo,pivot) :: ooo)
     ensures left == unskipAllInside(o,pivot)
{
}

lemma unskipAllInside_LEMMA5(o : Object, pivot : Object, rv : Owner)
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires rv ==  unskipAllInside(o,pivot)
    requires strictlyInside(o,pivot)
     ensures o in rv
     ensures (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo) <= rv
     ensures forall r <- rv :: (r == o) || (r in  (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo) )
    //  ensu
//    res rv <= {o} + (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo)
    //  ensures rv >= {o} + (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo)

{
  //  if (not(strictlyInside(o,pivot)))
  //     {
  //         assert unskipAllInside(o,pivot) == (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo);
  //     } else {
  //         assert unskipAllInside(o,pivot) == {o} + (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo);
  //     }
}







lemma unskipAllInside_LEMMA6(o : Object, pivot : Object)

   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
//  requires strictlyInside(o,pivot)
     ensures unskipAllInside(o,pivot)    == {o} + (set oo <- o.owner, ooo <- unskipAllInside(oo,pivot) :: ooo)
     ensures arghStrictlyInside(o,pivot) == {o} + (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo)
{}








lemma cunty_LEMMA3(o : Object, pivot : Object)
 //lifts asI==sAi to sets
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: argh(oo) == oo.AMFO

   // these two doesn't work
   //   ensures forall oo <- o.owner :: ((set ooo <- unskipAllInside(oo, pivot) :: ooo) == (set ooo <- arghStrictlyInside(oo, pivot) :: ooo))
   //   ensures (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo) == (set oo <- o.owner, ooo <- arghStrictlyInside(oo, pivot) :: ooo)

     ensures forall oo <- o.owner :: (set ooo <- argh(oo) :: ooo) == (set ooo <- oo.AMFO :: ooo)
     ensures (set oo <- o.owner, ooo <- (set x <- argh(oo)) :: ooo) == (set oo <- o.owner, ooo <- oo.AMFO :: ooo)
     ensures (set oo <- o.owner, ooo <- argh(oo) :: ooo) == (set oo <- o.owner, ooo <- oo.AMFO :: ooo)

{
   forall oo <- o.owner ensures ((set ooo <- argh(oo) :: ooo) == (set ooo <- oo.AMFO :: ooo))
      {
         assert argh(oo) == oo.AMFO;
      }

   assert forall oo <- o.owner ::  ((set ooo <- argh(oo) :: ooo) == (set ooo <- oo.AMFO :: ooo));
}




lemma cunty_LEMMA4(o : Object, pivot : Object)
 //lifts asI==sAi to sets
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: argh(oo) == oo.AMFO

     ensures (set oo <- o.owner, ooo <- argh(oo) :: ooo) == (set oo <- o.owner, ooo <- oo.AMFO :: ooo)
     ensures ({o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo)) == ({o} + (set oo <- o.owner, ooo <- oo.AMFO :: ooo))
     ensures argh(o) == ({o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo))
     ensures argh(o) == ({o} + (set oo <- o.owner, ooo <- oo.AMFO :: ooo))

{
  cunty_LEMMA3(o,pivot);
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


lemma  arghStrictlyInside_LEMMA5(o : Object, pivot : Object, arghIn : Owner)
  //control flow "inversion" of arghStrictlyInside...
  decreases o.AMFO
   requires o.Ready()
   requires pivot.Ready()
   requires arghIn == arghStrictlyInside(o, pivot)
   requires strictlyInside(o,pivot)
   // ensures arghIn == {o} + (set oo <- o.owner, ooo <- arghStrictlyInside(oo, pivot) :: ooo)
{
   assert arghIn == arghStrictlyInside(o, pivot);
   assert arghIn == allStrictlyInside(argh(o),pivot);
   assert arghIn == (set oo <- argh(o) | strictlyInside(oo,pivot));
   argh_LEMMA4(o);
   assert arghIn == (set oo <- ({o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo))  | strictlyInside(oo,pivot)); //ERR
}



lemma arghStrictlyInside_LEMMA6(o : Object, pivot : Object, arghIn : Owner)
  //control flow "inversion" of arghStrictlyInside...
  decreases o.AMFO
   requires o.Ready()
   requires pivot.Ready()
   requires strictlyInside(o,pivot)
   requires arghIn == (set oo <- argh(o) | strictlyInside(oo,pivot))
   // ensures arghIn == {o} + (set oo <- o.owner, ooo <- arghStrictlyInside(oo, pivot) :: ooo)
{
   assert arghIn == (set oo <- argh(o) | strictlyInside(oo,pivot));
   assert arghIn == (set oo <- ({o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo))  | strictlyInside(oo,pivot)); //ERR
}



lemma arghStrictlyInside_LEMMA7(o : Object, pivot : Object, arghIn : Owner)
  //control flow "inversion" of arghStrictlyInside...
  decreases o.AMFO
   requires o.Ready()
   requires pivot.Ready()
   requires strictlyInside(o,pivot)
   requires AllReady(arghIn)
   requires arghIn == argh(o)
    ensures argh(o) == o.AMFO
    ensures argh(o) == {o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo)   //ERR
   {
         argh_LEMMA4(o);
   }



// lemma unskipAllInside_LEMMA4(o : Object, pivot : Object)   //WORKS
//    decreases o.AMFO
//     requires o.Ready()
//     requires pivot.Ready()
//     requires strictlyInside(o,pivot)
//     requires forall oo <- o.owner ::  ((set ooo <- unskipAllInside(oo, pivot) :: ooo) == (set ooo <- arghStrictlyInside(oo, pivot) :: ooo))
//      ensures (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo) == (set oo <- o.owner, ooo <- arghStrictlyInside(oo, pivot) :: ooo)
// {}




//
// lemma skipAllInside_LEMMA1(next : Object, pivot : Object)  //FAILS
//    decreases next.AMFO
// //done : Owner,
// //    requires AllReady(done)
// //    requires done !! {next}
//     requires next.Ready()
//     requires pivot.Ready()
//      ensures (set x <- next.AMFO | strictlyInside(x,pivot)) == skipAllInside(next,pivot)
//
//     {
//       if (not(strictlyInside(next,pivot)))
//         {
//             assert skipAllInside(next,pivot) == {};
//             next.ExtraReady();
//             assert (set x <- next.AMFO | strictlyInside(x,pivot)) == {};
//             assert (set x <- next.AMFO | strictlyInside(x,pivot)) == skipAllInside(next,pivot);
//             return;
//         }
//
//       assert strictlyInside(next,pivot);
//
//       if (next.owner == {})
//        {
//           assert (set x <- next.AMFO | strictlyInside(x,pivot)) == skipAllInside(next,pivot);
//           return;
//        }
//
//        assert next.owner > {};
//
//        forall oo <- next.owner
//          ensures (set x <- oo.AMFO | strictlyInside(x,pivot)) == skipAllInside(oo,pivot)
//          {
//             skipAllInside_LEMMA1(oo,pivot);
//             assert (set x <- oo.AMFO | strictlyInside(x,pivot)) == skipAllInside(oo,pivot);
//          }
//
//        assert forall oo <- next.owner :: (set x <- oo.AMFO | strictlyInside(x,pivot)) == skipAllInside(oo,pivot);
//
//        assert (set oo <- next.owner, x <- oo.AMFO | strictlyInside(x,pivot) :: x) ==   ///oldERR
//                  (set oo <- next.owner, x <- skipAllInside(oo,pivot) :: x);
//
//
//         assert skipAllInside(next,pivot) == {next} + (set oo <- next.owner, ooo <- skipAllInside(oo,pivot) :: ooo);  //oldERR
//
//         assert (set x <- next.AMFO | strictlyInside(x,pivot))  //oldERR
//                      == {next} + (set oo <- next.owner, ooo <- oo.AMFO | strictlyInside(oo,pivot) :: ooo);
//     }
//




//
// lemma skipAllInside_LEMMA1x(o : Object, pivot : Object)  //WORKS DOESA NOTHING
//    decreases o.AMFO
//     requires o.Ready()
//     requires pivot.Ready()
//     requires strictlyInside(o,pivot)
//     requires forall oo <- o.owner :: (set x <- oo.AMFO | strictlyInside(x,pivot)) == skipAllInside(oo,pivot)
// //     ensures (set oo <- o.owner, ooo <- (set x <- oo.AMFO | strictlyInside(x,pivot)) :: ooo) == (set oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo)
// //     ensures (set oo <- o.owner, ooo <- oo.AMFO | strictlyInside(ooo,pivot) :: ooo) == (set oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo)
// {
// }



lemma skipAllInside_LEMMA1a(o : Object, pivot : Object)   ///DOESNT WORK - calls UNPROVED subLEMMERS
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
//    requires strictlyInside(o,pivot)
//     ensures forall oo <- o.owner :: allStrictlyInside(oo.AMFO,pivot) == skipAllInside(oo,pivot)
     ensures allStrictlyInside(o.AMFO,pivot) == skipAllInside(o,pivot)
{
      if (not(strictlyInside(o,pivot)))
        {
            assert skipAllInside(o,pivot) == {};
            o.ExtraReady();
            assert allStrictlyInside(o.AMFO,pivot) == {};
            assert allStrictlyInside(o.AMFO,pivot) == skipAllInside(o,pivot);
            return;
        }

      assert strictlyInside(o,pivot);

      if (o.owner == {})
       {
          assert allStrictlyInside(o.AMFO,pivot) == skipAllInside(o,pivot);
          return;
       }

       assert o.owner > {};

       forall oo <- o.owner
         ensures allStrictlyInside(oo.AMFO,pivot) == skipAllInside(oo,pivot)
         {
            skipAllInside_LEMMA1a(oo,pivot);
            assert allStrictlyInside(oo.AMFO,pivot) == skipAllInside(oo,pivot);
         }

       var aSI := (set oo <- o.owner, x <- allStrictlyInside(oo.AMFO,pivot) :: x);
       var sAI := (set oo <- o.owner, x <- skipAllInside(oo,pivot) :: x);

       assert forall oo <- o.owner :: allStrictlyInside(oo.AMFO,pivot) == skipAllInside(oo,pivot);
       skipAllInside_LEMMA1b(o,pivot);
       assert (set oo <- o.owner, x <- allStrictlyInside(oo.AMFO,pivot) :: x) == (set oo <- o.owner, x <- skipAllInside(oo,pivot) :: x);
       skipAllInside_LEMMA1c(o, pivot, aSI, sAI);  //COS THIS DOESNT WORK

       assert {o} + aSI == {o} + sAI;

       assert skipAllInside(o,pivot) == {o} + (set oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo);
       assert skipAllInside(o,pivot) == {o} + sAI;
       assert allStrictlyInside(o.AMFO,pivot) == {o} + aSI;
       assert allStrictlyInside(o.AMFO,pivot) == skipAllInside(o,pivot);
}


lemma skipAllInside_LEMMA1b(o : Object, pivot : Object)   //WORKS
 //lifts asI==sAi to sets
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: allStrictlyInside(oo.AMFO,pivot) == skipAllInside(oo,pivot)
     ensures forall oo <- o.owner :: (set ooo <- allStrictlyInside(oo.AMFO,pivot) :: ooo) == (set ooo <- skipAllInside(oo,pivot) :: ooo)
     ensures (set oo <- o.owner, ooo <- (set x <- allStrictlyInside(oo.AMFO,pivot)) :: ooo) == (set oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo)
     ensures (set oo <- o.owner, ooo <- allStrictlyInside(oo.AMFO,pivot) :: ooo) == (set oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo)
{
   forall oo <- o.owner ensures (set ooo <- allStrictlyInside(oo.AMFO,pivot) :: ooo) == (set ooo <- skipAllInside(oo,pivot) :: ooo)
      {
         assert allStrictlyInside(oo.AMFO,pivot) == skipAllInside(oo,pivot);
      }
}

lemma skipAllInside_LEMMA1c(o : Object, pivot : Object, aSI : Owner, sAI : Owner)   //DOESNT WORK
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: allStrictlyInside(oo.AMFO,pivot) == skipAllInside(oo,pivot)
    requires aSI == (set oo <- o.owner, ooo <- allStrictlyInside(oo.AMFO,pivot) :: ooo)
    requires sAI == (set oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo)
    requires aSI == sAI
     ensures {o} + aSI == {o} + sAI
     ensures allStrictlyInside(o.AMFO,pivot) == {o} + aSI    //ERR
     ensures skipAllInside(o,pivot) ==
         if (not(strictlyInside(o,pivot))) then ({}) else ({o} + sAI)
{
//assert allStrictlyInside(o.AMFO,pivot) == {};A

//(set o <- soup | strictlyInside(o,whole) )
}



lemma skipAllInside_LEMMA1d(o : Object, pivot : Object, aSI : Owner, sAI : Owner)  //DOESNT WORK
  /// version of skipAllInside_LEMMA1c - but using arghStrictlyInside
  /// WHAT NEEDS TO HAPPEN is to invert the polarity control flow?
  ///  from
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: arghStrictlyInside(o,pivot) == skipAllInside(oo,pivot)
    requires aSI == (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo)
    requires sAI == (set oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo)
    requires aSI == sAI

     ensures {o} + aSI == {o} + sAI
   //   ensures arghStrictlyInside(o,pivot) ==   // {o} + aSI  //xERR
   //       if (not(strictlyInside(o,pivot))) then ({}) else ({o} + aSI)
     ensures arghStrictlyInside(o,pivot) ==   // {o} + aSI  //ERR
         if (not(strictlyInside(o,pivot))) then ({}) else ({o} + aSI)

     ensures skipAllInside(o,pivot) ==
         if (not(strictlyInside(o,pivot))) then ({}) else ({o} + sAI)
{
   //can the lift-forall-to-set lemma help here?


   //make skipall inside just iterate of thre whole fucking AMDO
   //and pick each individsual ;node
   //rqather than stopping "early"?????
   //  **unskipAllInside** (or recAllInside)
}




lemma arghStrictlyInside_LEMMA1b(o : Object, pivot : Object)   //WORKS
 //lifts asI==sAi to sets
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: arghStrictlyInside(oo,pivot) == skipAllInside(oo,pivot)
     ensures forall oo <- o.owner :: (set ooo <- arghStrictlyInside(oo,pivot) :: ooo) == (set ooo <- skipAllInside(oo,pivot) :: ooo)
     ensures (set oo <- o.owner, ooo <- (set x <- arghStrictlyInside(oo,pivot)) :: ooo) == (set oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo)
     ensures (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo)
{
   forall oo <- o.owner ensures (set ooo <- arghStrictlyInside(oo,pivot) :: ooo) == (set ooo <- skipAllInside(oo,pivot) :: ooo)
      {
         assert arghStrictlyInside(oo,pivot) == skipAllInside(oo,pivot);
      }
}




// {:timeLimit 30}
lemma argh_LEMMA13(o : Object, pivot : Object)  //doesn't work without assume
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
     ensures arghStrictlyInside(o,pivot) == skipAllInside(o,pivot)//ERR
{
        if (not(strictlyInside(o,pivot)))
        {
            argh_LEMMA13a(o,pivot);
            assert arghStrictlyInside(o,pivot) == {};
            assert arghStrictlyInside(o,pivot) == skipAllInside(o,pivot) == {};
            return;
            }

      assert strictlyInside(o,pivot);

      if (o.owner == {})
       {
            assert skipAllInside(o,pivot) == {o};
            assert arghStrictlyInside(o,pivot) == {o};
            assert arghStrictlyInside(o,pivot) == skipAllInside(o,pivot) == {o};
            return;
       }

       assert o.owner > {};

       forall oo <- o.owner
         ensures arghStrictlyInside(oo,pivot) == skipAllInside(oo,pivot)
         {
           argh_LEMMA13(oo,pivot);
           assert arghStrictlyInside(oo,pivot) == skipAllInside(oo,pivot);
         }

arghStrictlyInside_LEMMA1b(o,pivot);

assert  (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo) ==
 (set oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo);

    //  assert arghStrictlyInside(o,pivot) == {o} + (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo);

      assert skipAllInside(o,pivot) == {o} + (set oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo);

// assume  arghStrictlyInside(o,pivot) == skipAllInside(o,pivot);
}


lemma  {:timeLimit 30} argh_LEMMA13a(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires not(strictlyInside(o,pivot))
     ensures arghStrictlyInside(o,pivot) == {}
{
   assert forall x <- o.AMFO :: not(strictlyInside(x,pivot));
   assert  arghStrictlyInside(o,pivot) == {};
}

//allStrictlyInside(argh(o),pivot)
// lemma {:timeLimit 30} argh_LEMMA13b(o : Object, pivot : Object)  //DOES NOTHING
//    decreases o.AMFO
//     requires o.Ready()
//     requires pivot.Ready()
//     requires (strictlyInside(o,pivot))
//     requires o.owner > {}
//  //    ensures arghStrictlyInside(o,pivot) == {o} + (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo);
// {
//   assert arghStrictlyInside(o,pivot)  == allStrictlyInside(argh(o),pivot);
// //  assert arghStrictlyInside(o,pivot)  == allStrictlyInside(argh(o),pivot);
// }

lemma {:timeLimit 30} argh_LEMMA13c(o : Object, a : Owner, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires a == argh(o)
    requires AllReady(a)
    requires pivot.Ready()
    requires (strictlyInside(o,pivot))
    requires o.owner > {}
    // ensures  arghStrictlyInside(o,pivot)  == (set o : Object <- argh(o) | strictlyInside(o,pivot) )
   //  ensures arghStrictlyInside(o,pivot) == allStrictlyInside(argh(o),pivot)
   //   ensures o.Ready()
   //   ensures argh(o) == argh(o)
     ensures allStrictlyInside(a,pivot) == (set o : Object <- a | strictlyInside(o,pivot))
     {
         argh_LEMMA3(o);
         argh_LEMMA13d(a,pivot);

         assert allStrictlyInside(a,pivot) == (set o : Object <- a | strictlyInside(o,pivot));
     }


lemma {:timeLimit 30} argh_LEMMA13d(oo : Owner, pivot : Object)
    requires AllReady(oo)
    requires pivot.Ready()
     ensures allStrictlyInside(oo,pivot) ==  (set o : Object <- oo | strictlyInside(o,pivot) )
   {}



function argh(o : Object) : (rv : Owner)
//clean recursive alter alternative definition of AMFO (recAmfo?) // recAllOwners
  decreases o.AMFO
  // requires o.Ready()
 { assume o.Ready();
   {o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo) }


// lemma argh_LEMMA00(o : Object)
// //establishes o.AMFO == argh(o)
//   decreases o.AMFO
//    requires o.Ready()
//  //   ensures argh(o) == ({o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo))
// {
//     assert argh(o) == o.AMFO by { argh_LEMMA0(o); }
//     assert argh(o) == ({o} + (set oo <- o.owner, ooo <- oo.AMFO :: ooo))
//       by { argh_LEMMA4(o); assert (argh(o) == ({o} + (set oo <- o.owner, ooo <- oo.AMFO :: ooo))); }
//     forall oo <- o.owner ensures (oo.AMFO == argh(oo)) {argh_LEMMA0(oo); }
//
//     assert argh(o) == ({o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo));
// }


// lemma argh_LEMMA00(o : Object)
// //establishes o.AMFO == argh(o)
//   decreases o.AMFO
//    requires o.Ready()
//     ensures argh(o) == ({o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo))
// {
//    if (o.owner == {}) {return;}
//
//    forall oo <- o.owner ensures (argh(oo) == ({oo} + (set xx <- oo.owner, xxx <- argh(xx) :: xxx)))
//    {
//       argh_LEMMA00(oo);
//       assert argh(oo) == ({oo} + (set xx <- oo.owner, xxx <- argh(xx) :: xxx));
//    }
//
//
//    forall oo <- o.owner ensures (argh(oo) == ({oo} + (set xx <- oo.owner, xxx <- argh(xx) :: xxx)))
//    {
//       argh_LEMMA00(oo);
//       assert argh(oo) == ({oo} + (set xx <- oo.owner, xxx <- argh(xx) :: xxx));
//    }
//
// //   assert forall oo <- o.owner :: (argh(oo) == ({oo} + (set xx <- oo.owner, xxx <- argh(xx) :: xxx)));
//
// }


lemma arghStrictlyInside_LEMMA0(o : Object)
//establishes o.AMFO == argh(o)
  decreases o.AMFO
   requires o.Ready()
    ensures o.AMFO == argh(o)
{
   if (o.owner == {}) {return;}

   forall oo <- o.owner ensures (true)
   {
      argh_LEMMA0(oo);
      assert argh(oo) == oo.AMFO;
   }
}


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

lemma argh_LEMMA5(o : Object)
  decreases o.AMFO
   requires o.Ready()
    ensures argh(o) == ({o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo))//ERR
{
     argh_LEMMA4(o);
     assert argh(o) == ({o} + (set oo <- o.owner, ooo <- oo.AMFO :: ooo));
     forall oo <- o.owner ensures (oo.AMFO == argh(oo)) { argh_LEMMA0(oo); }
     assert forall oo <- o.owner :: oo.AMFO == argh(oo);
     assert argh(o) == ({o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo));//ERR
}

lemma argh_LEMMA6(o : Object)
  decreases o.AMFO
   requires o.Ready()
    ensures argh(o) == ({o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo))//ERR
{
     argh_LEMMA4(o);
     assert argh(o) == ({o} + (set oo <- o.owner, ooo <- oo.AMFO :: ooo));
     forall oo <- o.owner ensures (oo.AMFO == argh(oo)) { argh_LEMMA0(oo); }
     assert argh(o) == ({o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo));//ERR
}




function amfoStrictlyInside(o : Object, pivot : Object) : Owner
  decreases o.AMFO
   requires o.Ready()
 { allStrictlyInside(
      o.AMFO,
//     {o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo),
     pivot) }

function arghStrictlyInside(o : Object, pivot : Object) : Owner
  decreases o.AMFO
   requires o.Ready()
 { allStrictlyInside(argh(o),pivot) }


lemma amfoSI_LEMMA0(o : Object, pivot : Object)
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



// lemma skipAllInside_LEMMA1e(o : Object, pivot : Object)   //WORKS
//    decreases o.AMFO
//     requires o.Ready()
//     requires pivot.Ready()
//     requires strictlyInside(o,pivot)
//      ensures forall oo <- o.owner :: allStrictlyInside(oo.AMFO,pivot) == skipAllInside(oo,pivot)
// {
//    if (not(strictlyInside(o,pivot))) { return; }
//
//    forall oo <- o.owner ensures (allStrictlyInside(oo.AMFO,pivot) == skipAllInside(oo,pivot))
//       {
//         if (not(strictlyInside(oo,pivot))) { return; }
//
//         skipAllInside_LEMMA1e(oo,pivot);
//         assert  forall ooo <- oo.owner :: allStrictlyInside(ooo.AMFO,pivot) == skipAllInside(ooo,pivot);
//         assert (set oo <- o.owner, ooo <- allStrictlyInside(oo.AMFO,pivot) :: ooo) == o.AMFX;
//
//       assert allStrictlyInside(oo.AMFO,pivot) == skipAllInside(oo,pivot);
//       }
// }
