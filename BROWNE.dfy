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

lemma skipAllInside_LEMMA1(next : Object, pivot : Object)  //FAILS
   decreases next.AMFO
//done : Owner,
//    requires AllReady(done)
//    requires done !! {next}
    requires next.Ready()
    requires pivot.Ready()
     ensures (set x <- next.AMFO | strictlyInside(x,pivot)) == skipAllInside(next,pivot)

    {
      if (not(strictlyInside(next,pivot)))
        {
            assert skipAllInside(next,pivot) == {};
            next.ExtraReady();
            assert (set x <- next.AMFO | strictlyInside(x,pivot)) == {};
            assert (set x <- next.AMFO | strictlyInside(x,pivot)) == skipAllInside(next,pivot);
            return;
        }

      assert strictlyInside(next,pivot);

      if (next.owner == {})
       {
          assert (set x <- next.AMFO | strictlyInside(x,pivot)) == skipAllInside(next,pivot);
          return;
       }

       assert next.owner > {};

       forall oo <- next.owner
         ensures (set x <- oo.AMFO | strictlyInside(x,pivot)) == skipAllInside(oo,pivot)
         {
            skipAllInside_LEMMA1(oo,pivot);
            assert (set x <- oo.AMFO | strictlyInside(x,pivot)) == skipAllInside(oo,pivot);
         }

       assert forall oo <- next.owner :: (set x <- oo.AMFO | strictlyInside(x,pivot)) == skipAllInside(oo,pivot);

       assert (set oo <- next.owner, x <- oo.AMFO | strictlyInside(x,pivot) :: x) ==   ///ERR
                 (set oo <- next.owner, x <- skipAllInside(oo,pivot) :: x);


        assert skipAllInside(next,pivot) == {next} + (set oo <- next.owner, ooo <- skipAllInside(oo,pivot) :: ooo);  //ERR

        assert (set x <- next.AMFO | strictlyInside(x,pivot))  //ERR
                     == {next} + (set oo <- next.owner, ooo <- oo.AMFO | strictlyInside(oo,pivot) :: ooo);
    }






lemma skipAllInside_LEMMA1x(o : Object, pivot : Object)  //WORKS DOESA NOTHING
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: (set x <- oo.AMFO | strictlyInside(x,pivot)) == skipAllInside(oo,pivot)
//     ensures (set oo <- o.owner, ooo <- (set x <- oo.AMFO | strictlyInside(x,pivot)) :: ooo) == (set oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo)
//     ensures (set oo <- o.owner, ooo <- oo.AMFO | strictlyInside(ooo,pivot) :: ooo) == (set oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo)
{
}



lemma skipAllInside_LEMMA1a(o : Object, pivot : Object)   ///DOESNT WORK
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
//    requires strictlyInside(o,pivot)
//     ensures forall oo <- o.owner :: allStrictlyInside(oo.AMFO,pivot) == skipAllInside(oo,pivot)
  ensures allStrictlyInside(o.AMFO,pivot) == skipAllInside(o,pivot)    //ERR
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

       assert forall oo <- o.owner :: allStrictlyInside(oo.AMFO,pivot) == skipAllInside(oo,pivot);
       skipAllInside_LEMMA1b(o,pivot);
       assert forall oo <- o.owner :: (set ooo <- allStrictlyInside(oo.AMFO,pivot) :: ooo) == (set ooo <- skipAllInside(oo,pivot) :: ooo);

       assert (set oo <- o.owner, x <- allStrictlyInside(oo.AMFO,pivot) :: x) == (set oo <- o.owner, x <- skipAllInside(oo,pivot) :: x);

        assert skipAllInside(o,pivot) == {o} + (set oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo);

      //   assert allStrictlyInside(o.AMFO,pivot)
      //                == {o} + (set oo <- o.owner, ooo <- allStrictlyInside(oo.AMFO,pivot)  :: ooo);
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


//
// lemma skipAllInside_LEMMA1c(o : Object, pivot : Object)
//    decreases o.AMFO
//     requires o.Ready()
//     requires pivot.Ready()
//     requires strictlyInside(o,pivot)
//      ensures o.AMFO == allStrictlyInside(o.AMFO,pivot)
//    //  ensures allStrictlyInside(o.AMFO,pivot) == {o} + (set oo <- o.owner, ooo <- allStrictlyInside(oo.AMFO,pivot)  :: ooo)
// {
//    assert o.AMFO == {o} + o.AMFX;
//    assert o.AMFX == (set oo <- o.owner, ooo <- oo.AMFO :: ooo);
// }


function argh(o : Object) : Owner
  decreases o.AMFO
   requires o.Ready()
 { {o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo) }

lemma argh_LEMMA0(o : Object)
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
  decreases o.AMFO
   requires o.Ready()
    ensures o.AMFO == ({o} + (set oo <- o.owner, ooo <- oo.AMFO :: ooo))
{}

lemma argh_LEMMA2(o : Object, pivot : Object)
  decreases o.AMFO
   requires o.Ready()
   requires not(strictlyInside(o,pivot))
    ensures forall oo <- o.owner :: not(strictlyInside(oo,pivot))
    ensures forall oo <- o.AMFO  :: not(strictlyInside(oo,pivot))
{}

function amfoStrictlyInside(o : Object, pivot : Object) : Owner
  decreases o.AMFO
   requires o.Ready()
 { allStrictlyInside(
     {o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo),
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
  //  ensures amfoStrictlyInside(o,pivot) == allStrictlyInside(argh(o),pivot)
   //  ensures amfoStrictlyInside(o,pivot) == allStrictlyInside(argh(o),pivot)
   //  ensures amfoStrictlyInside(o,pivot) == allStrictlyInside(o.AMFO,pivot)
{
      calc {
         allStrictlyInside(argh(o),pivot);
      }


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
// //ERR        assert allStrictlyInside(oo.AMFO,pivot) == skipAllInside(oo,pivot);
//       }
// }
