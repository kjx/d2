include "Ownership.dfy"


//
//
//   assert (set x <- next.AMFO | strictlyInside(x,m.o)) == skipAllInside(next,m.o);
//   assert (set x <- cext.AMFO | strictlyInside(x,m.c)) == skipAllInside(cext,m.c);


function skipAllInside(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
    {
      if (not(strictlyInside(o,pivot))) then ({})
          else  {o} + (set oo <- o.owner, ooo <- skipAllInside(oo, pivot) :: ooo)
    }

function unskipAllInside(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
    {
      if (not(strictlyInside(o,pivot))) then (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo)
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
  decreases o.AMFO
   requires o.Ready()
   requires (not(strictlyInside(o,pivot)))
    ensures unskipAllInside(o, pivot) == {}
   {
      forall oo <- o.owner
        ensures (unskipAllInside(o, pivot) == {})
        {
         argh_LEMMA2(oo,pivot);
         assert (not(strictlyInside(oo,pivot)));
         unskipAllInside_LEMMA1(oo,pivot);
         assert unskipAllInside(o, pivot) == {};
        }

   }

lemma {:timeLimit 60} unskipAllInside_LEMMA2(o : Object, pivot : Object, unskip : Owner)
  decreases o.AMFO
   requires o.Ready()
   requires strictlyInside(o,pivot)
   requires unskip == unskipAllInside(o,pivot)
//    ensures unskipAllInside(o, pivot) == {o} + (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo)
{

assert o in unskip;

assert strictlyInside(o,pivot);

forall oo <- o.owner, ooo <- unskipAllInside(oo, pivot)
  ensures true
    {
      if (strictlyInside(oo,pivot))
        {

        }
    }



 assert unskipAllInside(o,pivot) ==  //ERR
       if (not(strictlyInside(o,pivot))) then (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo)
          else  {o} + (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo);

}

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



lemma skipAllInside_LEMMA1a(o : Object, pivot : Object)   ///DOESNT WORK
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

lemma skipAllInside_LEMMA1c(o : Object, pivot : Object, aSI : Owner, sAI : Owner)   //DIESBT WOIRKJ
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
lemma argh_LEMMMA3(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
     ensures arghStrictlyInside(o,pivot) == skipAllInside(o,pivot)
{
        if (not(strictlyInside(o,pivot)))
        {
            argh_LEMMMA3a(o,pivot);
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
           argh_LEMMMA3(oo,pivot);
           assert arghStrictlyInside(oo,pivot) == skipAllInside(oo,pivot);
         }

arghStrictlyInside_LEMMA1b(o,pivot);

assert  (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo) ==
 (set oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo);

    //  assert arghStrictlyInside(o,pivot) == {o} + (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo);

      assert skipAllInside(o,pivot) == {o} + (set oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo);

assume  arghStrictlyInside(o,pivot) == skipAllInside(o,pivot);
}


lemma  {:timeLimit 30} argh_LEMMMA3a(o : Object, pivot : Object)
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
lemma {:timeLimit 30} argh_LEMMMA3b(o : Object, pivot : Object)  //DOES NOTHING
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires (strictlyInside(o,pivot))
    requires o.owner > {}
 //    ensures arghStrictlyInside(o,pivot) == {o} + (set oo <- o.owner, ooo <- arghStrictlyInside(oo,pivot) :: ooo);
{
  assert arghStrictlyInside(o,pivot)  == allStrictlyInside(argh(o),pivot);



//  assert arghStrictlyInside(o,pivot)  == allStrictlyInside(argh(o),pivot);

}

lemma {:timeLimit 30} argh_LEMMMA3c(o : Object, a : Owner, pivot : Object)
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
         argh_LEMMMA3d(a,pivot);

         assert allStrictlyInside(a,pivot) == (set o : Object <- a | strictlyInside(o,pivot));
     }


lemma {:timeLimit 30} argh_LEMMMA3d(oo : Owner, pivot : Object)
    requires AllReady(oo)
    requires pivot.Ready()
     ensures allStrictlyInside(oo,pivot) ==  (set o : Object <- oo | strictlyInside(o,pivot) )
   {}



function argh(o : Object) : (rv : Owner)
//clean recursive alter alternative definition of AMFO (recAmfo?)
  decreases o.AMFO
  // requires o.Ready()
 { assume o.Ready();
   {o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo) }

lemma argh_LEMMA0(o : Object)
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
 //deconstructs AMFO to iteration over *owners*
  decreases o.AMFO
   requires o.Ready()
    ensures AllReady( argh(o) )
{
   argh_LEMMA0(o);
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
