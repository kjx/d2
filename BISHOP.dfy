//include "Ownership-Recursive.dfy"
include "Ownership-Parallel.dfy"
include "Context.dfy"


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
