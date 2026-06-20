//include "Ownership-Recursive.dfy"
include "Ownership-Parallel.dfy"
include "Context.dfy"


lemma {:verify false} All_Fucked_Up (obelow : Owner, oabove : Owner, cbelow : Owner, cabove : Owner, m : Klon)
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
    var oaOF := allOutsideFlatten(obelow,m.o) - m.o.AMFO;
    var caOF := allOutsideFlatten(cbelow,m.c) - m.c.AMFO;

// assert oaOF == caOF; //shouldnt work!  //BUIT IT DOESS!!!!!!Q!

    var oSBF := allStrictlyBelowFlatten(obelow,m.o);
    var cSBF := allStrictlyBelowFlatten(cbelow,m.c);

// assert cSBF == mapThruKlon(oSBF, m);


}



function allOutsideFlatten(ownrs : OWNR, pivot : Object) : (rv : Owner)
 //or allFlatOutside or allOutsideFlat?    all => returns set;
//flattens ownrs, returns all those that are outside/above the pivot
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()
  ensures AllReady(rv)
{ set x <- flatten(ownrs) | outside(x,pivot) } // not(strictlyInside(x, pivot)) }


function allStrictlyBelowFlatten(ownrs : OWNR, pivot : Object) : (rv : Owner)
//flattens ownrs, returns all those that are strictlyInside/beloiw the pivot - or allStricltInsideFlat
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()
  ensures AllReady(rv)
{ set x <- flatten(ownrs) | strictlyInside(x,pivot) } // not(strictlyInside(x, pivot)) }


function allStrictlyBelowFlattenMap(ownrs : OWNR, m : Klon) : (rv : Owner)
//maps owners thru klon, flattens ownrs, returns all those that are strictlyInside/beloiw the pivot
     reads m.hns()
  requires AllReady(flatten(ownrs))
  requires klonReady(m)
  requires klonCalid(m)
  requires ownrs <= m.m.Keys

   ensures AllReady(rv)
   ensures forall r <- rv    :: strictlyInside(r, m.c)
   ensures forall o <- ownrs :: klonLine(o, m.m[o], m)
  // ensures rv <= m.m.Values
  // ensures forall b <- mapBackKlon(rv,m) :: strictlyInside(b, m.o)
{ set x : Object <- flatten(mapThruKlon(ownrs, m)) | strictlyInside(x, m.c) }











function allOwnersInsidePivot(o : Object, pivot : Object) : (rv : Owner)
//flattens ownrs, returns all those that are inside the pivot -
  requires o.Ready()
  requires pivot.Ready()
   ensures AllReady(rv)
   ensures forall r <- rv :: recInside(r, pivot)
   ensures forall oo <- o.AMFO :: recInside(oo,pivot) ==> oo in rv
   ensures forall r <- rv :: inside(r, pivot)
   ensures forall oo <- o.AMFO :: inside(oo,pivot) ==> oo in rv
 {
     set x <- o.AMFO | inside(x,pivot)
 }


function allOwnersRecInsidePivot(o : Object, pivot : Object) : (rv : Owner)
//flattens ownrs, returns all those that are inside the pivot -
  requires o.Ready()
  requires pivot.Ready()
   ensures AllReady(rv)
   ensures forall r <- rv :: recInside(r, pivot)
   ensures forall oo <- o.AMFO :: recInside(oo,pivot) ==> oo in rv
   ensures forall r <- rv :: inside(r, pivot)
   ensures forall oo <- o.AMFO :: inside(oo,pivot) ==> oo in rv
 {
     set x <- o.AMFO | recInside(x,pivot)
 }


function allOwnersMinusPivot(o : Object, pivot : Object) : (rv : Owner)
//flattens ownrs, returns all those that are strictlyInside/beloiw the pivot - or allStricltInsideFlat
  requires o.Ready()
  requires pivot.Ready()
  requires strictlyInside(o,pivot)
   ensures AllReady(rv)
//   ensures forall r <- rv :: inside(r, pivot)
   ensures forall oo <- o.AMFO :: inside(oo,pivot) ==> oo in rv
 {
     o.AMFO - pivot.AMFX
 }



lemma INSIDE_MINUS_PIVOT(o : Object, pivot : Object)
   requires o.Ready()
   requires pivot.Ready()
   requires strictlyInside(o,pivot)
    ensures allOwnersMinusPivot(o,pivot) == allOwnersInsidePivot(o,pivot)
    ensures allOwnersMinusPivot(o,pivot) == allOwnersRecInsidePivot(o,pivot)
    ensures allOwnersInsidePivot(o,pivot) == allOwnersRecInsidePivot(o,pivot)
{}














function allOwnersStrictlyInsidePivot(o : Object, pivot : Object) : (rv : Owner)
//flattens ownrs, returns all those that are strictlyInside/beloiw the pivot - or allStricltInsideFlat
  requires o.Ready()
  requires pivot.Ready()
   ensures AllReady(rv)
   ensures forall r <- rv :: strictlyInside(r, pivot)
 {
     set x <- o.AMFO | strictlyInside(x,pivot)
 }

function allOwnersStrictlyMinusPivot(o : Object, pivot : Object) : (rv : Owner)
//flattens ownrs, returns all those that are strictlyInside/beloiw the pivot - or allStricltInsideFlat
  requires o.Ready()
  requires pivot.Ready()
  requires strictlyInside(o,pivot)
   ensures AllReady(rv)
//   ensures forall r <- rv :: strictlyInside(r, pivot)
 {
     o.AMFO - pivot.AMFO
 }