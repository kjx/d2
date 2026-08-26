include "Ownership.dfy"
include "Set-Lemmata.dfy"

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
















































// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

lemma unskipAllInside_LEMMA0(o : Object, pivot : Object, skip : Owner, unskip : Owner)
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
  //unskip is always from transitive ownerhsip (AMFO/argh)
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


lemma unskipAllInside_LEMMA2(o : Object, pivot : Object, arghIn : Owner, unskip : Owner)
  //unskip equals arghInside
  //rplaced with _LEMMA1*
  decreases o.AMFO
   requires o.Ready()
   requires pivot.Ready()
   requires arghIn == arghStrictlyInside(o, pivot)
   requires unskip == unskipAllInside(o, pivot)

    ensures unskip == arghIn
   {
     unskipAllInside_LEMMA1z(o,pivot);
   }


lemma unskipAllInside_LEMMA3(o : Object, pivot : Object)
 //given unskipAllInside owners == arghStrictlyInside owners
 //then  set of unskips is set of arghStrictlyInside
//not really used (much)
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

// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

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

lemma {:verify false} skipAllInside_LEMMA1c(o : Object, pivot : Object, aSI : Owner, sAI : Owner)   //DOESNT WORK
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: allStrictlyInside(oo.AMFO,pivot) == skipAllInside(oo,pivot)
    requires aSI == (set oo <- o.owner, ooo <- allStrictlyInside(oo.AMFO,pivot) :: ooo)
    requires AllReady(aSI)
    requires sAI == (set oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo)
    requires AllReady(sAI)
    requires aSI == sAI
     ensures {o} + aSI == {o} + sAI
     ensures allStrictlyInside(o.AMFO,pivot) == {o} + aSI    //ERR
     ensures skipAllInside(o,pivot) ==
         if (not(strictlyInside(o,pivot))) then ({}) else ({o} + sAI)
{
//assert allStrictlyInside(o.AMFO,pivot) == {};A

//(set o <- soup | strictlyInside(o,whole) )
}



lemma {:verify false} skipAllInside_LEMMA1d(o : Object, pivot : Object, aSI : Owner, sAI : Owner)  //DOESNT WORK
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
   //   ensures forall oo <- o.owner :: ((set ooo <- unskipAllInside(oo, pivot) :: ooo) == (set ooo <- arghStrictlyInside(oo, pivot) :: ooo))
   //   ensures (set oo <- o.owner, ooo <- unskipAllInside(oo, pivot) :: ooo) == (set oo <- o.owner, ooo <- arghStrictlyInside(oo, pivot) :: ooo)

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
     ensures skipAllInside(o,pivot) == amfoStrictlyInside(o,pivot)
{
   unskipAllInside_LEMMA0(o,pivot, skipAllInside(o, pivot), unskipAllInside(o, pivot));
    assert skipAllInside(o,pivot) == unskipAllInside(o,pivot);
   unskipAllInside_LEMMA1z(o, pivot);
    assert unskipAllInside(o, pivot) == arghStrictlyInside(o,pivot);
   arghStrictlyInside_LEMMA0(o,pivot);
    assert arghStrictlyInside(o,pivot) == amfoStrictlyInside(o,pivot);
}


lemma {:verify false} argh_LEMMA13orig(o : Object, pivot : Object)  //doesn't work without assume
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
