//include "Ownership-Recursive.dfy"
include "Ownership-Parallel.dfy"
include "Context.dfy"


predicate enclosedBy(part : Object, whole : Object)
  requires part.Ready()
  requires whole.Ready()
{
   && (part.AMFO >= whole.AMFO)
   && (forall p <- part.AMFO  :: (p in whole.AMFO) || (p.AMFO >= whole.AMFO))
}

predicate enclosedBy1(part : Object, whole : Object)
  requires part.Ready()
  requires whole.Ready()
{
    inside(part, whole) &&
    forall p <- part.AMFO  :: (p in whole.AMFO) || (p.AMFO >= whole.AMFO)
}

predicate recEnclosedBy(part : Object, whole : Object)
     requires part.Ready()
    decreases part.AMFO
{
  || (part == whole)
  || (forall x <- part.owner :: recEnclosedBy(x,whole))
}

lemma Enclosed_Enclosed(part : Object, whole : Object)
  requires part.Ready()
  requires whole.Ready()
   ensures enclosedBy(part,whole) == recEnclosedBy(part,whole)
   {
    if (part == whole)
      {
        assert enclosedBy(part,whole) == recEnclosedBy(part,whole);
        return;
      }
    forall x <- part.owner ensures (enclosedBy(x,whole) == recEnclosedBy(x,whole) ) //by
      {

      }

   }



lemma HappyFamilies(soup : set<Object>, whole : Object, ins: set<Object>, outs: set<Object>, sides: set<Object>)
  requires ins   == allInside(soup, whole)
  requires outs  == allOutside(soup, whole)
  requires sides == allOffside(soup, whole)
   ensures soup  == ins + outs + sides
{}

predicate Xoffside(part : Object, whole : Object) reads {} { not(colinear(part.AMFO,whole.AMFO)) }



lemma prattt(part : Object)
  requires part.Ready()
   ensures forall x <- part.AMFO :: x in part.AMFO
{}

lemma SLICE_X_DICE(a : Object, amfo : OWNR, pivot : Object, below : OWNR, above : OWNR, aside : Owner)
    //give that below == amfo - pivot.AMFO,
    //then below + pivot.AMFO == amfo
    requires a.Ready()
    requires amfo == a.AMFO
 requires AllReady(amfo)
 requires pivot.Ready()
 requires AllReady(below)
 requires AllReady(above)
 requires AllReady(aside)
  ensures isFlat(amfo)
 requires amfo > pivot.AMFO
  ensures strictlyInside(a,pivot)
//nope requires forall x <- below :: x.AMFO > pivot.AMFO    //stops ""side loadung"""
//  requires below == amfo - pivot.AMFO
  requires below == (set x <- amfo | strictlyInside(x,pivot))
  requires above == (set x <- amfo | inside(pivot,x))
  requires aside == amfo - (above + below)
   ensures aside == (set x <- amfo | not(strictlyInside(x,pivot)) && not(inside(pivot,x)))
   ensures aside == (set x <- amfo | not(strictlyInside(x,pivot) || inside(pivot,x)))
   ensures aside == (set x <- amfo | not(inside(x,pivot) || inside(pivot,x)))
   ensures aside == (set x <- amfo | not(colinear(x.AMFO, pivot.AMFO)))
   ensures aside == (set x <- amfo | offside(x, pivot))


   ensures below !! above !! aside

   ensures amfo == below + above + aside

    //  ensures pivot.AMFO == (set x <- amfo | not(strictlyInside(x,pivot)))
//   ensures above <= pivot.AMFO
////   ensures above >= pivot.AMFO
  //  ensures below + pivot.AMFO == amfo
  //  ensures amfo == pivot.AMFO + below
  //  ensures forall x <- below :: (x in amfo) //&& (strictlyInside(x, pivot))
  //  ensures forall x <- below :: x !in pivot.AMFO
  // //nope ensures forall x <- below :: (strictlyInside(x, pivot))
  //  ensures below >= (set x <- amfo | strictlyInside(x, pivot))
  // //nope ensures below <= (set x <- amfo | strictlyInside(x, pivot))
  {}













lemma WhyDoesntThisWork(o : Object, pivot : Object, remainder : Owner)
  requires o.Ready()
  requires pivot.Ready()
  requires strictlyInside(o, pivot)
  requires remainder == (o.AMFO - pivot.AMFO)
   ensures o.AMFO > pivot.AMFO
   ensures isFlat(o.AMFO)
   ensures (o.AMFO - pivot.AMFO) >= (set x <- o.AMFO | x !in pivot.AMFO)
   ensures (o.AMFO - pivot.AMFO) <= (set x <- o.AMFO | x !in pivot.AMFO)
   ensures remainder == (set x <- o.AMFO | x !in pivot.AMFO)
   ensures remainder == (o.AMFO - pivot.AMFO)


//   ensures (o.AMFO - pivot.AMFO) >= (set x <- o.AMFO | x.AMFO >= pivot.AMFO)
 //  ensures (o.AMFO - pivot.AMFO) <= (set x <- o.AMFO | x.AMFO <= pivot.AMFO)




   ensures forall x <- pivot.AMFO :: x in o.AMFO
   ensures forall x <- pivot.AMFO :: o.AMFO >= pivot.AMFO >= x.AMFO

   ensures forall r <- remainder :: (r in o.AMFO) && (r !in pivot.AMFO)

//   ensures forall r <- remainder :: (r in o.AMFO) && (r !in pivot.AMFO)

   ensures forall r <- remainder :: (r.AMFO > pivot.AMFO)

///  ensures forall x <- o.AMFO, p <- pivot.AMFO ::  ????

    ensures forall x <- o.AMFO :: (x in remainder) == (x !in pivot.AMFO)
   //    ensures remainder == (set x <- o.AMFO | x.AMFO !in pivot.AMFO)
{}

lemma singel(o : Object)
  requires o.Ready()
  // requires AllReady(oo)
  // requires isFlat(oo)
  // requires oo > {}n
  // ensures forall o <- oo, xx <- o.AMFO :: xx in oo
//   ensures exists x <- oo :: forall y <- oo :: x.AMFO >= y.AMFO
   ensures exists x <- o.AMFO :: x.AMFO == o.AMFO
{}



lemma All_Fucked_Up(obelow : Owner, oabove : Owner, cbelow : Owner, cabove : Owner, m : Klon)
  requires AllReady(obelow)
  requires AllReady(oabove)
  requires AllReady(cbelow)
  requires AllReady(cabove)
  requires klonReady(m)
  requires klonCalid(m)
  requires obelow <= m.m.Keys
  requires oabove <= m.m.Keys
  requires flatten(obelow) >= flatten(oabove)
  requires cbelow == mapThruKlon(obelow, m)
  requires cabove == mapThruKlon(oabove, m)

//   ensures flatten(cbelow) >= flatten(cabove)
{
    var fAoB := flatAbove(obelow,m.o) - m.o.AMFO;
    var fAcB := flatAbove(cbelow,m.c) - m.c.AMFO;

assert fAoB == fAcB; //shouldnt work!
}



function flatAbove(ownrs : OWNR, pivot : Object) : (rv : Owner)
//flattens ownrs, returns all those that are outside/above the pivot
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()
  ensures AllReady(rv)
{ set x <- flatten(ownrs) | outside(x,pivot) } // not(strictlyInside(x, pivot)) }
