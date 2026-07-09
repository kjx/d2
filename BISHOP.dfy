//include "Ownership-Recursive.dfy"
include "Ownership-Parallel.dfy"
include "Context.dfy"

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

  ensures forall x <- o.AMFO, p <- pivot.AMFO ::

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
