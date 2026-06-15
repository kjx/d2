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

   ensures flatten(cbelow) >= flatten(cabove)
{}