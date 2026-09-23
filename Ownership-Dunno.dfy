include "Ownership.dfy"
include "Ownership-Trilemma.dfy"

//named cos I didn't know whwat else to call it
//perhaps functions wiht the PIVOT stay here ("Onwership-Pivot")
//functions with the KLON goto Klon-Ownership or **Klon-Pivot**
//the NUKE methods I think are all DEAD
//the ones w'ere running with now are flowner -> flatten owner  flowner(owners,pivot) -> flattened owners :-)

function nuke(soup : Owner) : OWNR {assume forall s <- soup :: s.Ready(); (set o <- soup, oo <- o.AMFO :: oo)}

lemma FLATTEN_NUKE(soup : Owner)
  ensures nuke(soup) == flatten(soup)
{
  assume forall s <- soup :: s.Ready();
  assert forall s <- soup :: s in s.AMFO;
  forall s <- soup ensures (true)
  {
    forall t <- s.AMFO ensures (true)
    {
        assert t in nuke({s});
        assert t in flatten({s});
     }
     assert forall n <-    nuke({s}) :: n in s.AMFO;
     assert forall f <- flatten({s}) :: f in s.AMFO;
     assert s.AMFO == nuke({s}) == flatten({s});
  }
}

function nukeOutside(soup : OWNR, pivot : Object) : (rv : Owner)
 requires forall s <- soup :: s.Ready()
//  ensures forall s <- soup, o <- s.AMFO | outside(s,pivot) :: outside(o,pivot)
 requires pivot.Ready()
  ensures forall r <- rv :: outside(r,pivot)
//ensures rv == flatten( (set s <- soup | outside(s,pivot)) )
     {  MaybeOutiesSidies(soup, pivot);
      flatten( set s <- soup | outside(s,pivot) ) }


function nukeInside(soup : OWNR, pivot : Object) : (rv : Owner)
 requires forall s <- soup :: s.Ready()
//  ensures forall s <- soup, o <- s.AMFO | outside(s,pivot) :: outside(o,pivot)
 requires pivot.Ready()
     { flatten( set s <- soup | inside(s,pivot) ) }


function nukeStrictlyInside(soup : OWNR, pivot : Object) : (rv : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
     {      flatten( set s <- soup | strictlyInside(s,pivot) ) }


function nukePivotlyOutside(soup : OWNR, pivot : Object) : (rv : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
     {      flatten( set s <- soup | pivotlyOutside(s,pivot) ) }




function nukeStrictlyPivot(soup : OWNR, pivot : Object) : (rv : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
 ensures (pivot in soup)  <==> (rv == pivot.AMFO)
 ensures (pivot !in soup) <==> (rv == {})
 requires pivot.Ready()
     { flatten( set s <- soup | s == pivot ) }


lemma FLATTEN_SUM4(a : Owner, b : Owner, c : Owner, cc : Owner)
  requires a+b+c == cc
  ensures flatten(a) + flatten(b) + flatten(c) == flatten(cc)
{}


lemma nukeEmAll1(soup : OWNR, pivot : Object)
 //verifies on the comnmand line subn 13 sep
   requires forall s <- soup :: s.Ready()
   requires pivot.Ready()
{
   assert forall s <- soup ::  outside(s,pivot) != inside(s,pivot);

   assert soup ==
              (set s <- soup | outside(s,pivot) ) +
              (set s <- soup | inside(s,pivot) );

   assert forall s <- soup | inside(s,pivot) :: (s == pivot) != strictlyInside(s,pivot);

   assert (set s <- soup | inside(s,pivot)) ==
              (set s <- soup | (s == pivot) ) +
              (set s <- soup | strictlyInside(s,pivot) );

    assert soup ==
              (set s <- soup | outside(s,pivot) ) +
              (set s <- soup | (s == pivot) ) +
              (set s <- soup | strictlyInside(s,pivot) );

}

lemma nukeEmAll2(soup : OWNR, pivot : Object, sOut : OWNR, sIn : OWNR, sSIn : OWNR, sSPv : OWNR)
 //verifies on the comnmand line subn 13 sep
   requires forall s <- soup :: s.Ready()
   requires pivot.Ready()
   requires sOut == (set s <- soup | outside(s,pivot))
   requires sIn  == (set s <- soup | inside(s,pivot))
   requires sSIn == (set s <- soup | strictlyInside(s,pivot) )
   requires sSPv == (set s <- soup | s == pivot )
    ensures sIn  == sSIn + sSPv
    ensures soup == sIn + sOut
    ensures soup == sOut + sSIn + sSPv
{
   assert forall s <- soup :: outside(s,pivot) != inside(s,pivot);
   assert forall s <- soup | inside(s,pivot) :: strictlyInside(s,pivot) != (s == pivot);
}

lemma nukeEmAll3(soup : OWNR, pivot : Object, nOut : OWNR, nSIn : OWNR, nSPv : OWNR, foup : OWNR)
 //verifies on the comnmand line subn 13 sep
   requires forall s <- soup :: s.Ready()
   requires pivot.Ready()
   requires nOut == nukeOutside(soup, pivot)
   requires nSIn == nukeStrictlyInside(soup, pivot)
   requires nSPv == nukeStrictlyPivot(soup, pivot)
   requires foup == flatten( soup )
    ensures nOut + nSIn + nSPv == foup
{
   assert forall s <- soup :: outside(s,pivot) != inside(s,pivot);
   assert forall s <- soup | inside(s,pivot) :: strictlyInside(s,pivot) != (s == pivot);

   var sOut := (set s <- soup | outside(s,pivot) );
   var sSIn := (set s <- soup | strictlyInside(s,pivot) );
   var sSPv := (set s <- soup | s == pivot );
   var sIn  := (set s <- soup | inside(s,pivot) );

   nukeEmAll2(soup, pivot, sOut, sIn, sSIn, sSPv);
   assert sIn == sSIn + sSPv;
   assert soup == sIn + sOut;
   assert soup == sOut + sSIn + sSPv;

   assert nOut == flatten( sOut );
   assert nSIn == flatten( sSIn );
   assert nSPv == flatten( sSPv );

   FLATTEN_SUM4(sOut, sSIn, sSPv, soup);

   assert flatten(soup) == foup;
   assert flatten(sOut + sSIn + sSPv) == foup;
   assert flatten(sOut) + flatten(sSIn) + flatten(sSPv) == foup;
   assert nOut + nSIn + nSPv == foup;
}



lemma nukeEmAll3F(soup : OWNR, pivot : Object, nOut : OWNR, nSIn : OWNR, nSPv : OWNR, foup : OWNR)
 //verifies on the comnmand line subn 13 sep
   requires forall s <- soup :: s.Ready()
   requires pivot.Ready()
   requires nOut == nukeOutside(soup, pivot)
   requires nSIn == nukeStrictlyInside(soup, pivot)
   requires nSPv == nukeStrictlyPivot(soup, pivot)
   requires foup == flatten( soup )
    ensures nOut + nSIn + nSPv == foup
{
   assert forall s <- soup :: outside(s,pivot) != inside(s,pivot);
   assert forall s <- soup | inside(s,pivot) :: strictlyInside(s,pivot) != (s == pivot);

   var sOut := (set s <- soup | outside(s,pivot) );
   var sSIn := (set s <- soup | strictlyInside(s,pivot) );
   var sSPv := (set s <- soup | s == pivot );
   var sIn  := (set s <- soup | inside(s,pivot) );

   nukeEmAll2(soup, pivot, sOut, sIn, sSIn, sSPv);
   assert sIn == sSIn + sSPv;
   assert soup == sIn + sOut;
   assert soup == sOut + sSIn + sSPv;

   assert nOut == flatten( sOut );
   assert nSIn == flatten( sSIn );
   assert nSPv == flatten( sSPv );

   FLATTEN_SUM4(sOut, sSIn, sSPv, soup);

   assert flatten(soup) == foup;
   assert flatten(sOut + sSIn + sSPv) == foup;
   assert flatten(sOut) + flatten(sSIn) + flatten(sSPv) == foup;
   assert nOut + nSIn + nSPv == foup;
}



lemma nukeEmAll4F(soup : OWNR, pivot : Object, nOut : OWNR, nSIn : OWNR, nSPv : OWNR, foup : OWNR)
 //verifies on the comnmand line subn 13 sep
   requires forall s <- soup :: s.Ready()
   requires pivot.Ready()
   requires nOut == nukeOutside(soup, pivot)
   requires nSIn == nukeStrictlyInside(soup, pivot)
   requires nSPv == nukeStrictlyPivot(soup, pivot)
   requires foup == flatten( soup )
//    ensures (nOut + nSPv) !! nSIn
    {

    }


///Oh SHIT 0 most of the these are WRONG.
 function flattenInside(soup : OWNR, pivot : Object) : (rv : Owner)
  ensures forall r <- rv :: inside(r,pivot)
  ensures forall r <- flatten(soup) :: inside(r,pivot) ==> r in rv
{ set x <- flatten(soup) | inside(x,pivot) }

function flattenOutside(soup : OWNR, pivot : Object) : (rv : Owner)
  ensures forall r <- rv :: outside(r,pivot)
  ensures forall r <- flatten(soup) :: outside(r,pivot) ==> r in rv
{ set x <- flatten(soup) | outside(x,pivot) }

function flattenOffside(soup : OWNR, pivot : Object) : (rv : Owner)
  ensures forall r <- rv :: offside(r,pivot)
  ensures forall r <- flatten(soup) :: offside(r,pivot) ==> r in rv
{ set x <- flatten(soup) | offside(x,pivot) }

function flattenStrictlyInside(soup : OWNR, pivot : Object) : (rv : Owner)
  ensures forall r <- rv :: strictlyInside(r,pivot)
  ensures forall r <- flatten(soup) :: strictlyInside(r,pivot) ==> r in rv
{ set x <- flatten(soup) | strictlyInside(x,pivot) }

function flattenPivotlyOutside(soup : OWNR, pivot : Object) : (rv : Owner)
  ensures forall r <- rv :: pivotlyOutside(r,pivot)
  ensures forall r <- flatten(soup) :: pivotlyOutside(r,pivot) ==> r in rv
{ set x <- flatten(soup) | pivotlyOutside(x,pivot) }


predicate insidePivot(o : Object, pivot : Object, owner : Object) : (rv : bool)   reads {}   { inside(o, pivot) && inside(o,owner) }
  //o >= pivot is a selecwtion condition for this case
  //o >= owner should be fucken built the fuck in

lemma LEMMA_insidePivot(o : Object, pivot : Object, owner : Object)
   requires inside(o,owner)
    ensures insidePivot(o,pivot,owner) == inside(o,pivot)
{}

predicate onlyPivot(o : Object, pivot : Object, owner : Object) : (rv : bool)   reads {}   { inside(o, pivot) && inside(o,owner) &&  inside(pivot, owner) }
predicate exceptPivot(o : Object, pivot : Object, owner : Object) : (rv : bool) reads {}   { inside(o, pivot) && inside(o,owner) && outside(pivot, owner) }
   //should we explicitly require owner in o.AMFO  aka o inside owner?
   //well apart from the "preconditions to the preconditions" problem

function shortcutOnlyPivot(soup : OWNR, pivot : Object) : (rv : Owner)
  ensures forall p <- pivot.AMFO :: inside(pivot, p)
  ensures forall r <- rv :: inside(pivot, r)
  ensures (rv == {}) != (rv == pivot.AMFO)
  ensures (forall s <- soup :: outside(s,pivot)) ==> (rv == {})
  ensures (exists s <- soup ::  inside(s,pivot)) ==> (rv == pivot.AMFO)
  ensures forall r <- rv :: inside(pivot, r)
  ensures forall r <- rv :: exists s <- soup :: onlyPivot(s, pivot, r)
  ensures forall r <- rv :: r.Ready()
  { assume forall s <- soup :: s.Ready(); assume pivot.Ready();
    if (exists s <- soup :: inside(s,pivot)) then (pivot.AMFO) else {} }

function flattenOnlyPivot(soup : OWNR, pivot : Object)  : (rv : Owner)
 {set s <- soup, oo <- s.AMFO | onlyPivot(s,pivot,oo) :: oo}

function flattenExceptPivot(soup : OWNR, pivot : Object) : (rv : Owner)
 {set s <- soup, oo <- s.AMFO | exceptPivot(s,pivot,oo) :: oo}

function flatteninsidePivot(soup : OWNR, pivot : Object) : (rv : Owner)
 {set s <- soup, oo <- s.AMFO | insidePivot(s,pivot,oo) :: oo}


lemma LEMMA_flattenOnlyPivot0(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == flattenOnlyPivot(soup, pivot))
   ensures forall r <- rv :: inside(pivot, r)
   ensures forall r <- rv :: exists s <- soup :: onlyPivot(s,pivot,r)
{}

lemma LEMMA_flattenOnlyPivot1(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == flattenOnlyPivot(soup, pivot))

  requires forall s <- soup :: outside(s,pivot)
   ensures rv == {}
{}

lemma LEMMA_flattenOnlyPivot2(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == flattenOnlyPivot(soup, pivot))

  requires exists s <- soup ::  inside(s,pivot)
   ensures rv <= pivot.AMFO
{
  var s :| s in soup && inside(s,pivot);

  forall r <- rv ensures (r in pivot.AMFO) //by
   {

      assert inside(pivot,r);
      AXIOMAMFOREVERSE(pivot, r);
   }
  assert rv <= pivot.AMFO;
}

lemma LEMMA_flattenOnlyPivot3(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == flattenOnlyPivot(soup, pivot))

  requires exists s <- soup ::  inside(s,pivot)
   ensures rv >= pivot.AMFO
{
   var s :| s in soup && inside(s,pivot);
   assert forall r <- s.AMFO     | onlyPivot(s,pivot,r) :: inside(pivot, r);
   assert forall r <- s.AMFO     | onlyPivot(s,pivot,r) :: r in rv;

   assert rv >= pivot.AMFO;
}

lemma LEMMA_flattenOnlyPivot9(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == flattenOnlyPivot(soup, pivot))
   ensures (forall s <- soup :: outside(s,pivot)) ==> (rv == {})
   ensures (exists s <- soup ::  inside(s,pivot)) ==> (rv == pivot.AMFO)
{
  if (forall s <- soup :: outside(s,pivot))
     { LEMMA_flattenOnlyPivot1(soup,pivot,rv); return; }
    else
    { LEMMA_flattenOnlyPivot2(soup,pivot,rv); LEMMA_flattenOnlyPivot3(soup,pivot,rv); }
}

lemma LEMMA_shortcutOnlyPivot0(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == shortcutOnlyPivot(soup, pivot))

   ensures forall r <- rv :: inside(pivot, r)
   ensures forall r <- rv :: exists s <- soup :: inside(s,r)
   ensures forall r <- rv :: inside(pivot, r) && (exists s <- soup :: inside(s,r))
   ensures forall r <- rv :: exists s <- soup :: onlyPivot(s,pivot,r)
{}

lemma LEMMA_shortcutOnlyPivot1(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == shortcutOnlyPivot(soup, pivot))
   ensures (forall s <- soup :: outside(s,pivot)) ==> (rv == {})
   ensures (exists s <- soup ::  inside(s,pivot)) ==> (rv >  {})
   ensures (exists s <- soup ::  inside(s,pivot)) ==> (rv == pivot.AMFO)
{}

lemma LEMMA_flattenExceptPivot0(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == flattenExceptPivot(soup, pivot))
   ensures forall r <- rv :: outside(pivot,r) && (exists s <- soup :: inside(s,r))
   ensures forall r <- rv :: exists s <- soup :: exceptPivot(s,pivot,r)
   ensures forall r <- rv :: exists s <- soup :: inside(s, pivot) && inside(s,r) && outside(pivot, r)
   //ensures forall r <- rv :: exists s <- soup :: exceptPivot(s,pivot,r) && pivotlyOutside(r,pivot)

   ensures rv <= flatten(soup)
   //  ensures (forall s <- soup :: outside(s,pivot) ==> (s in rv))
  //  ensures (forall s <- soup, oo <- s.AMFO, ooo <- oo.AMFO | outside(ooo,pivot) :: (ooo in rv))
   // ensures (rv == {}) ==> (forall s <- soup, oo <- s.AMFO :: colinear(oo.AMFO,pivot.AMFO))
{
  if (rv == {}) { return; }

  var s :| s in soup && inside(s,pivot);
  assert forall r <- s.AMFO     | exceptPivot(s,pivot,r) :: r in rv;


}

lemma LEMMA_shortcutVSflatten2(soup : OWNR, pivot : Object, shOP : Owner, fOP : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires shOP == shortcutOnlyPivot(soup, pivot)
  requires fOP == flattenOnlyPivot(soup, pivot)
  requires forall r <- shOP :: r.Ready()
  requires forall r <- fOP  :: r.Ready()
   ensures shOP == fOP
   ensures (shOP == fOP == {}) || (shOP == fOP == pivot.AMFO)
{
  if (forall s <- soup :: not(inside(s,pivot)))
    { assert shOP == fOP == {}; return; }

  assert exists s <- soup :: inside(s,pivot);
  LEMMA_flattenOnlyPivot9(soup,pivot,fOP);
  assert shOP == fOP == pivot.AMFO;
}


lemma TRICHOTOMY_ONLY_EXCEPT(o : Object, pivot : Object, owner : Object)
   ensures   onlyPivot(o,pivot,owner) ==> (inside(o,pivot) && inside(o,owner))
   ensures exceptPivot(o,pivot,owner) ==> (inside(o,pivot) && inside(o,owner))

   ensures outside(o, pivot) ==> (onlyPivot(o,pivot,owner) == exceptPivot(o,pivot,owner) == false)
   ensures (inside(o,pivot) && inside(o,owner))   ==> (onlyPivot(o,pivot,owner) != (exceptPivot(o,pivot,owner)))
{
  assume o.Ready();
  assume pivot.Ready();
  assume owner.Ready();
}


// inside(o, pivot) && inside(o,owner) &&  inside(pivot, owner)
// inside(o, pivot) && inside(o,owner) && outside(pivot, owner)


lemma OWNERZ_OF_PIVOTRY(soup : set<Object>, pivot : Object, fEP : Owner, fOP : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
 requires fEP == flattenExceptPivot(soup,pivot)
 requires fOP == flattenOnlyPivot(soup,pivot)
  ensures forall r <- fEP :: exists s <- soup :: exceptPivot(s,pivot,r)
  ensures forall r <- fOP :: exists s <- soup ::   onlyPivot(s,pivot,r)
  ensures forall r <- fEP :: exists s <- soup :: exceptPivot(s,pivot,r)
  ensures forall r <- fOP :: exists s <- soup ::   onlyPivot(s,pivot,r)
    {}


//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// pivotlyOutside - pivotlyOutside(x,pivot)
//   onlyPivot -  inside(pivot,owner)
//   exceptPivot -outside(pivot,owner)
lemma FUCKING_WIT_DA_PIVOT(pivot : Object, owner : Object)
  requires pivot.Ready()
  requires owner.Ready()
    ensures pivotlyOutside(owner,pivot) == not(owner.AMFO > pivot.AMFO)
    ensures  inside(pivot,owner) == (pivot.AMFO >= owner.AMFO)
    ensures outside(pivot,owner) == not(pivot.AMFO >= owner.AMFO)

    ensures    (pivot.AMFO >= owner.AMFO) ==> not(owner.AMFO > pivot.AMFO)
    ensures           inside(pivot,owner) ==> pivotlyOutside(owner,pivot)
//    ensures outside(pivot, owner) ==> pivotlyOutside(owner,pivot)
//  ensures not(pivot.AMFO >= owner.AMFO) ==> not(owner.AMFO > pivot.AMFO)
    {}


//////////////////////////////////////////////////////////////////////////////////////////////////////////////////



lemma FUCKING_WIT_pivotlyOutside(a : Object, b : Object)
  requires a.Ready()
  requires b.Ready()
  requires pivotlyOutside(a,b)
   ensures not(a.AMFO > b.AMFO)
   ensures (a.AMFO == b.AMFO) || not(a.AMFO >= b.AMFO)
    {}

lemma FUCKING_WIT_DA_except_PIVOT(a : Object, b : Object, c : Object)
  requires a.Ready()
  requires b.Ready()
  requires c.Ready()

  requires exceptPivot(a,b,c)
    ensures inside(a, b) && inside(a,c) && outside(b, c)
    ensures (a.AMFO >= b.AMFO) && (a.AMFO >= c.AMFO) && not(b.AMFO >= c.AMFO)
  //  ensures not(c.AMFO > b.AMFO)
  //  ensures pivotlyOutside(c,b)
    {}

lemma TRICHOTOMY_DICHOTOMY(soup : Owner, pivot : Object, left0 : Owner, left1 : Owner, right : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
 requires left0 == flattenStrictlyInside(soup,pivot)
 requires left1 == flattenPivotlyOutside(soup,pivot)
 requires right == flatten(soup)

  ensures left0 <= right
  ensures left1 <= right
  ensures left0 + left1 <= right
  ensures left0 + left1 >= right
  ensures left0 + left1 == right
 {}


lemma DICHOTOMY_TRICHOTOMY(soup : Owner, pivot : Object, left0 : Owner, left1 : Owner, right : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
 requires left0 == flattenExceptPivot(soup,pivot)
 requires left1 == flattenOnlyPivot(soup,pivot)
 requires right == flattenPivotlyOutside(soup,pivot)

//  ensures left0 <= right
  ensures left1 <= right
//  ensures left0 + left1 <= right
  // ensures left0 + left1 >= right
  // ensures left0 + left1 == right
{}

lemma NUKE_TRICHOTOMY_DICHOTOMY(soup : Owner, pivot : Object, left0 : Owner, left1 : Owner, right : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
 requires left0 == nukeStrictlyInside(soup,pivot)
 requires left1 == nukePivotlyOutside(soup,pivot)
 requires right == nuke(soup)

  ensures left0 <= right
  ensures left1 <= right
  ensures left0 + left1 <= right
  ensures left0 + left1 >= right
  ensures left0 + left1 == right
 {}


lemma NUKE_DICHOTOMY_TRICHOTOMY(soup : Owner, pivot : Object, left0 : Owner, left1 : Owner, right : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
 requires left0 == flattenExceptPivot(soup,pivot)
 requires left1 == flattenOnlyPivot(soup,pivot)
 requires right == flatteninsidePivot(soup,pivot)

  ensures left0 <= right
  ensures left1 <= right
  ensures left0 + left1 <= right
  ensures left0 + left1 >= right
  ensures left0 + left1 == right
{}





lemma INSIDE_VS_OUTSIDE(o : Object, whole : Object)
  requires o.Ready()
  requires whole.Ready()
  requires inside(o, whole)
  requires whole != o
   ensures outside(whole,o)
{}


lemma AFMO_ALWAYS_INSIDE(o : Object, whole : Object)
  requires o.Ready()
  requires whole.Ready()

  requires whole in o.AMFO
   ensures inside(o, whole)
{}




  // onlyPibot   --  inside(o, pivot) &&  inside(pivot, owner)
  // exceptPivot  -- inside(o, pivot) && outside(pivot, owner)

  //



lemma EXCEPT_EXCEPT_PIVOT(o : Object, pivot : Object, owner : Object)
  requires o.Ready()
  requires owner.Ready()
  requires pivot.Ready()

  requires owner in o.AMFO
   ensures inside(o, owner)
   ensures ( ||  ( inside(o,pivot) &&  inside(owner,pivot))
             ||  ( inside(o,pivot) && outside(owner,pivot))
             ||  (outside(o,pivot) && outside(owner,pivot)) )

   ensures  not( (outside(o,pivot) &&  inside(owner,pivot)) )

   ensures inside(owner,pivot) <==> (strictlyInside(owner,pivot) || (owner == pivot))

   ensures pivotlyOutside(owner,pivot) <==> (outside(owner,pivot) || (owner == pivot))

   ensures inside(pivot, owner) != outside(pivot, owner)
          //onlyPivot (inside) || exceptPivot (outside)

   ensures       ( inside(o,pivot) &&  inside(owner,pivot) ) <==>
           ( ||  ( inside(o,pivot) && strictlyInside(owner,pivot))
             ||  ( inside(o,pivot) && (owner == pivot) ) )


   ensures ( ||  ( inside(o,pivot) && strictlyInside(owner,pivot))  //fully inside
             ||  ( inside(o,pivot) && pivotlyOutside(owner,pivot))
             ||  (outside(o,pivot) && outside(owner,pivot)) )       //fully outside

   ensures ( ||  (     inside(o,pivot)       && strictlyInside(owner,pivot))  //fully inside
             ||  (  onlyPivot(o,pivot,owner) && pivotlyOutside(owner,pivot))  //is the pivot
             ||  (exceptPivot(o,pivot,owner) && pivotlyOutside(owner,pivot))  //insife from outside not  pivot
             ||  (    outside(o,pivot)       && outside(owner,pivot)) )       //fully outside


ensures (onlyPivot(o,pivot,owner) || exceptPivot(o,pivot,owner)) ==> inside(o,pivot)
ensures outside(o,pivot) != (inside(o,pivot) || onlyPivot(o,pivot,owner) || exceptPivot(o,pivot,owner))
ensures strictlyInside(owner,pivot) != pivotlyOutside(owner,pivot)




   ensures  (inside(o,pivot) && pivotlyOutside(owner,pivot)) ==>
                     (onlyPivot(o,pivot,owner) != exceptPivot(o,pivot,owner))

   ensures  (inside(o,pivot) && strictlyInside(owner,pivot)) ==>
                     (onlyPivot(o,pivot,owner) != exceptPivot(o,pivot,owner))

   ensures (insidePivot(o, pivot, owner)) <==>
                     (onlyPivot(o,pivot,owner) || exceptPivot(o,pivot,owner))

   ensures (inside(o, pivot)) <==>
                     (onlyPivot(o,pivot,owner) || exceptPivot(o,pivot,owner))

   ensures insidePivot(o,pivot,owner) == (onlyPivot(o,pivot,owner) || exceptPivot(o,pivot,owner))

   ensures ownerInsidePivot(o,pivot,owner) ==
                             (ownerOnlyPivot(o,pivot,owner) || ownerExceptPivot(o,pivot,owner))

///ensures (inside(o, pivot) && strictlyInside(owner,pivot))  ?


///ensures strictlyInside(owner,pivot)  ==>  inside(pivot, owner)
///ensures strictlyInside(owner,pivot) <==   inside(pivot, owner)

   ensures strictlyInside(owner,pivot)  ==>  not(inside(pivot, owner))
///ensures strictlyInside(owner,pivot) <==   not(inside(pivot, owner))

   ensures strictlyInside(owner,pivot)  ==> outside(pivot, owner)
///   ensures strictlyInside(owner,pivot) <==  outside(pivot, owner)

///ensures strictlyInside(owner,pivot)  ==> not(outside(pivot, owner))
///ensures strictlyInside(owner,pivot) <==  not(outside(pivot, owner))





///ensures pivotlyOutside(owner,pivot)  ==>  inside(pivot, owner)
   ensures pivotlyOutside(owner,pivot) <==   inside(pivot, owner)

///ensures pivotlyOutside(owner,pivot)  ==>  not(inside(pivot, owner))
///ensures pivotlyOutside(owner,pivot) <==   not(inside(pivot, owner))

///ensures pivotlyOutside(owner,pivot)  ==> outside(pivot, owner)
///ensures pivotlyOutside(owner,pivot) <==  outside(pivot, owner)

///ensures pivotlyOutside(owner,pivot)  ==> not(outside(pivot, owner))
   ensures pivotlyOutside(owner,pivot) <==  not(outside(pivot, owner))



ensures (inside(o,pivot) && pivotlyOutside(owner,pivot) &&  inside(pivot, owner)) ==> onlyPivot(o,pivot,owner)
ensures (inside(o,pivot) && pivotlyOutside(owner,pivot) && outside(pivot, owner)) ==> exceptPivot(o,pivot,owner)

ensures (inside(o,pivot) && strictlyInside(owner,pivot) &&  inside(pivot, owner)) ==> onlyPivot(o,pivot,owner)
ensures (inside(o,pivot) && strictlyInside(owner,pivot) && outside(pivot, owner)) ==> exceptPivot(o,pivot,owner)


ensures (inside(o,pivot)                                &&  inside(pivot, owner)) ==> onlyPivot(o,pivot,owner)
ensures (inside(o,pivot)                                && outside(pivot, owner)) ==> exceptPivot(o,pivot,owner)



ensures  strictlyInside(owner,pivot) ==> inside(o,pivot)
ensures  strictlyInside(owner,pivot) ==> strictlyInside(o,pivot)




////ensures ( inside(o, pivot) && pivotlyOutside(owner,pivot))  ==>  inside(pivot, owner)
//
////ensures (outside(o, pivot) && pivotlyOutside(owner,pivot))  ==>  outside(pivot, owner)

////ensures (onlyPivot(o,pivot,owner) || exceptPivot(o,pivot,owner)) ==> (pivotlyOutside(owner,pivot))


   ensures  inside(o,pivot)  != outside(o,pivot)
   ensures  inside(owner,pivot) != outside(owner,pivot)
{}

lemma FORALL_AMFO_PART_OWNER(soup : OWNR, sludge : Owner, pivot : Object)
  requires AllReady(soup)
  requires pivot.Ready()

   ensures forall o <- soup, owner <- o.AMFO :: (
    && inside(o,owner)
   // && ((inside(o, pivot) &&  inside(pivot, owner))  ==> outside(owner, pivot) )

    )

   ensures nuke(soup) == (set o <- soup,  owner <- o.AMFO :: owner)
{}


  //  ensures ( ||  (     inside(o,pivot)       && strictlyInside(owner,pivot))  //ownerStrictlyInside
  //            ||  (  onlyPivot(o,pivot,owner) && pivotlyOutside(owner,pivot))  //owner
  //            ||  (exceptPivot(o,pivot,owner) && pivotlyOutside(owner,pivot))  //insife from outside not  pivot
  //            ||  (    outside(o,pivot)       && outside(owner,pivot)) )       //fully outside

predicate ownerStrictlyInside(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {strictlyInside(owner,pivot)}

predicate ownerPivotlyOutside(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {pivotlyOutside(owner,pivot)}

predicate ownerFullyOutside(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {outside(owner,pivot) &&  outside(o,pivot)}

predicate ownerOnlyPivot(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {pivotlyOutside(owner,pivot) && onlyPivot(o,pivot,owner)}
predicate ownerExceptPivot(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {pivotlyOutside(owner,pivot) && exceptPivot(o,pivot,owner)}
predicate ownerInsidePivot(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {pivotlyOutside(owner,pivot) && insidePivot(o,owner,pivot)}




lemma PART_INSIDE_OWNER(soup : OWNR, pivot : Object)
  requires AllReady(soup) && pivot.Ready()
  ensures forall o <- soup, owner <- o.AMFO :: inside(o, owner)
  ensures forall o <- soup :: o.Ready()
{}



function flownerAll(soup : Owner) : OWNR {assume forall s <- soup :: s.Ready(); (set o <- soup, oo <- o.AMFO :: oo)}
  //yes same as nuke() etc...

function flownerStrictlyInside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(soup) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerStrictlyInside(o,pivot,owner) :: owner}
function flownerFullyOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(soup) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerFullyOutside(o,pivot,owner) :: owner}

function flownerOnlyPivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(soup) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerOnlyPivot(o,pivot,owner) :: owner}
function flownerExceptPivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(soup) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerExceptPivot(o,pivot,owner) :: owner}
function flownerInsidePivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(soup) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerInsidePivot(o,pivot,owner) :: owner}

 function flownerEverythingOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(soup) && pivot.Ready()
 { flownerFullyOutside(soup,pivot) + flownerInsidePivot(soup,pivot) }
 function flownerPivotlyOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(soup) && pivot.Ready()
   {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerPivotlyOutside(o,pivot,owner) :: owner}

lemma FLOWNER_EVERYTHING_OUTSIDE(soup : OWNR, pivot : Object)
  requires AllReady(soup) && pivot.Ready()
   ensures flownerEverythingOutside(soup,pivot) == flownerPivotlyOutside(soup,pivot)
{}
//could merge these two, but thiss lets us be more specific when calling them,
lemma FLOWNER_EVERYTHING_EVERYTHING(soup : OWNR, pivot : Object)
  requires AllReady(soup) && pivot.Ready()
   ensures flownerEverythingOutside(soup,pivot) == flownerFullyOutside(soup,pivot) + flownerInsidePivot(soup,pivot)
   ensures flownerEverythingOutside(soup,pivot) == flownerFullyOutside(soup,pivot) + (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))
{}

lemma FLOWNER_EVERYTHING_EVERYWHERE(soup : OWNR, pivot : Object, FEO : Owner, FFO : Owner, FOP : Owner, FEP : Owner)
  requires AllReady(soup) && pivot.Ready()
  requires FEO == flownerEverythingOutside(soup,pivot)
  requires FFO == flownerFullyOutside(soup,pivot)
  requires FOP == flownerOnlyPivot(soup,pivot)
  requires FEP == flownerExceptPivot(soup,pivot)
   ensures FEO == FFO + FOP + FEP
   ensures flownerEverythingOutside(soup,pivot) == flownerFullyOutside(soup,pivot) + (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))
{}

lemma FLOWNER_ALL_EVERYTHING(soup : OWNR, pivot : Object, ALL : Owner, SIN : Owner, FFO : Owner, FOP : Owner, FEP : Owner)
  requires AllReady(soup) && pivot.Ready()
  requires ALL == flownerAll(soup)
  requires SIN == flownerStrictlyInside(soup,pivot)
  requires FFO == flownerFullyOutside(soup,pivot)
  requires FOP == flownerOnlyPivot(soup,pivot)
  requires FEP == flownerExceptPivot(soup,pivot)
   ensures ALL == SIN + FFO + FOP + FEP
   ensures flownerAll(soup) == flownerStrictlyInside(soup,pivot) + flownerFullyOutside(soup,pivot) + (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))
{
  FLOWNER_ALL_ALL(soup, pivot);
}


lemma FLOWNER_DISJOINT(soup : OWNR, pivot : Object)
  requires AllReady(soup) && pivot.Ready()
   ensures flownerOnlyPivot(soup,pivot) !! flownerExceptPivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerOnlyPivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerExceptPivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerOnlyPivot(soup,pivot) !! flownerExceptPivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerInsidePivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerFullyOutside(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot) + flownerFullyOutside(soup,pivot))
   ensures flownerStrictlyInside(soup,pivot) !! (flownerInsidePivot(soup,pivot) + flownerFullyOutside(soup,pivot))
{}


lemma FLOWNER_CONJOINT(soup : OWNR, pivot : Object, FIO : Owner, FOP : Owner, FEP : Owner)
  requires AllReady(soup) && pivot.Ready()
  requires FOP == flownerOnlyPivot(soup,pivot)
  requires FEP == flownerExceptPivot(soup,pivot)
  requires FIO == flownerInsidePivot(soup,pivot)
   ensures FIO == FOP + FEP
   ensures flownerInsidePivot(soup,pivot) == (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))
{
   forall o <- soup, owner <- o.AMFO ensures (true) //by
     {
      PART_INSIDE_OWNER(soup,pivot);
      assert inside(o, owner);

      assert (owner in FOP) ==>  (owner in FIO);
      assert (owner in FEP) ==>  (owner in FIO);
      assert (owner in FIO) ==> ((owner in FOP) || (owner in FEP));
      assert (owner in FIO) ==> ((owner in FOP) != (owner in FEP));

      assert ownerOnlyPivot(o,pivot,owner)   ==>  pivotlyOutside(owner,pivot) && onlyPivot(o,pivot,owner);
      assert ownerExceptPivot(o,pivot,owner) ==>  pivotlyOutside(owner,pivot) && exceptPivot(o,pivot,owner);

      assert ownerOnlyPivot(o,pivot,owner)   <==  pivotlyOutside(owner,pivot) && onlyPivot(o,pivot,owner);
      assert ownerExceptPivot(o,pivot,owner) <==  pivotlyOutside(owner,pivot) && exceptPivot(o,pivot,owner);

      assert ownerOnlyPivot(o,pivot,owner)   <==> pivotlyOutside(owner,pivot) && onlyPivot(o,pivot,owner);
      assert ownerExceptPivot(o,pivot,owner) <==> pivotlyOutside(owner,pivot) && exceptPivot(o,pivot,owner);

      assert flownerInsidePivot(soup,pivot) >= FIO;
      assert flownerInsidePivot(soup,pivot) <= FIO;  //ERR

//      assert ownerInsidePivot(o,pivot,owner) == insidePivot(o,owner,pivot);

//      assert flownerInsidePivot(soup,pivot) >= FIO;

     }
}




lemma FLOWNER_JOINT(soup : OWNR, pivot : Object, FIO : Owner, FOP : Owner, FEP : Owner)
 //delete in favour of FLOWNER_ALL_ALL?
  requires AllReady(soup) && pivot.Ready()
  requires FOP == flownerOnlyPivot(soup,pivot)
  requires FEP == flownerExceptPivot(soup,pivot)
  requires FIO == flownerInsidePivot(soup,pivot)
   ensures FIO == FOP + FEP
   ensures FOP !! FEP
{}



lemma FLOWNER_JOINT2(soup : OWNR, pivot : Object, FA : Owner, FB : Owner, FC : Owner)
  requires AllReady(soup) && pivot.Ready()
  requires FA == flownerAll(soup)
  requires FB == flownerStrictlyInside(soup,pivot)
  requires FC == flownerPivotlyOutside(soup,pivot)
   ensures FA == FB + FC
   ensures FB !! FC
{}


lemma FLOWNER_JOINT2x2(soup0 : OWNR, soup1 : OWNR, pivot : Object)
  requires AllReady(soup0) && AllReady(soup1) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
   ensures flownerStrictlyInside(soup0,pivot) !! flownerPivotlyOutside(soup0,pivot)
   ensures flownerStrictlyInside(soup1,pivot) !! flownerPivotlyOutside(soup1,pivot)
//   ensures flownerStrictlyInside(soup0,pivot) >= flownerStrictlyInside(soup1,pivot)
//   ensures flownerPivotlyOutside(soup0,pivot) >= flownerPivotlyOutside(soup1,pivot)
//   ensures (flownerStrictlyInside(soup0,pivot) + flownerStrictlyInside(soup1,pivot))
//    !! (flownerStrictlyInside(soup0,pivot) + flownerPivotlyOutside(soup1,pivot))
{}



lemma FLOWNER_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
  requires AllReady(soup0) && AllReady(soup1) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
//   ensures flownerStrictlyInside(soup0,pivot)    >= flownerStrictlyInside(soup1,pivot)
//   ensures flownerFullyOutside(soup0,pivot)      >= flownerFullyOutside(soup1,pivot)
//   ensures flownerOnlyPivot(soup0,pivot)         >= flownerOnlyPivot(soup1,pivot)
//   ensures flownerExceptPivot(soup0,pivot)       >= flownerExceptPivot(soup1,pivot)
//   ensures flownerInsidePivot(soup0,pivot)       >= flownerInsidePivot(soup1,pivot)
//   ensures flownerEverythingOutside(soup0,pivot) >= flownerEverythingOutside(soup1,pivot)
   ensures flownerPivotlyOutside(soup0,pivot)    >= flownerPivotlyOutside(soup1,pivot)

{
 assert flownerPivotlyOutside(soup0,pivot)
   == (set o <- soup0, owner <- o.AMFO | PART_INSIDE_OWNER(soup0,pivot); ownerPivotlyOutside(o,pivot,owner) :: owner);
 assert flownerPivotlyOutside(soup0,pivot)
   == (set o <- soup0, owner <- o.AMFO | PART_INSIDE_OWNER(soup0,pivot); pivotlyOutside(owner,pivot) :: owner);
 assert flownerPivotlyOutside(soup0,pivot)
   == (set owner <- flownerAll(soup0) | PART_INSIDE_OWNER(soup0,pivot); pivotlyOutside(owner,pivot) :: owner);
 assert flownerPivotlyOutside(soup1,pivot)
   == (set o <- soup1, owner <- o.AMFO | PART_INSIDE_OWNER(soup1,pivot); ownerPivotlyOutside(o,pivot,owner) :: owner);
 assert flownerPivotlyOutside(soup1,pivot)
   == (set o <- soup1, owner <- o.AMFO | PART_INSIDE_OWNER(soup1,pivot); pivotlyOutside(owner,pivot) :: owner);
 assert flownerPivotlyOutside(soup1,pivot)
   == (set owner <- flownerAll(soup1) | PART_INSIDE_OWNER(soup1,pivot); pivotlyOutside(owner,pivot) :: owner);
 assert flownerAll(soup0) >= flownerAll(soup1);
 assert (set owner <- flownerAll(soup0) | PART_INSIDE_OWNER(soup0,pivot); pivotlyOutside(owner,pivot) :: owner)
     >= (set owner <- flownerAll(soup1) | PART_INSIDE_OWNER(soup1,pivot); pivotlyOutside(owner,pivot) :: owner);
 assert flownerPivotlyOutside(soup0,pivot)    >= flownerPivotlyOutside(soup1,pivot);
}

lemma flownerPivotlyOutside_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
  requires AllReady(soup0) && AllReady(soup1) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
//   ensures flownerStrictlyInside(soup0,pivot)    >= flownerStrictlyInside(soup1,pivot)
//   ensures flownerFullyOutside(soup0,pivot)      >= flownerFullyOutside(soup1,pivot)
//   ensures flownerOnlyPivot(soup0,pivot)         >= flownerOnlyPivot(soup1,pivot)
//   ensures flownerExceptPivot(soup0,pivot)       >= flownerExceptPivot(soup1,pivot)
//   ensures flownerInsidePivot(soup0,pivot)       >= flownerInsidePivot(soup1,pivot)
//   ensures flownerEverythingOutside(soup0,pivot) >= flownerEverythingOutside(soup1,pivot)
   ensures flownerPivotlyOutside(soup0,pivot)    >= flownerPivotlyOutside(soup1,pivot)





lemma flownerOnlyPivot_RESULT(soup : Owner, pivot : Object, rv : Owner)
//verified 23Sep2026
  requires AllReady(soup) && pivot.Ready() && AllReady(rv)
  requires flownerOnlyPivot(soup,pivot) == rv
   ensures (pivot  in flownerAll(soup))  ==> (rv == pivot.AMFO)
   ensures (pivot !in flownerAll(soup)) ==> (rv == {})
   {
   assert rv == flownerOnlyPivot(soup, pivot);
FLOWNER_SHORTCUT_OnlyPivot(soup, pivot, rv);
   assert rv == shortcutOnlyPivot(soup, pivot);
 LEMMA_shortcutOnlyPivot1(soup, pivot, rv);
   }

lemma flownerOnlyPivot_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
////verified 23Sep2026
  requires AllReady(soup0) && AllReady(soup1) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
   ensures flownerOnlyPivot(soup0,pivot)  >= flownerOnlyPivot(soup1,pivot)
{
  var rv0 := flownerOnlyPivot(soup0,pivot);
  flownerOnlyPivot_RESULT(soup0,pivot,rv0);
  var rv1 := flownerOnlyPivot(soup1,pivot);
  flownerOnlyPivot_RESULT(soup1,pivot,rv1);
  assert flownerOnlyPivot(soup0,pivot)     >= flownerOnlyPivot(soup1,pivot);
}




// forall o1 <- soup1, owner1 <- o1.AMFO | insidePivot(o1,pivot,owner1) ensures owner1 in flownerAll(soup0) {}

// forall s1 <- soup1, owner1 <- s1.AMFO | insidePivot(s1,pivot,owner1) ensures owner1 in flownerInsidePivot(soup0,pivot) {}

// assert forall s1 <- soup1,5 owner1 <- s1.AMFO | insidePivot(s1,pivot,owner1) :: owner1 in flownerInsidePivot(soup0,pivot);

// assert forall s1 <- soup1, owner1 <- s1.AMFO | ownerPivotlyOutside(s1,pivot,owner1) :: owner1 in flownerPivotlyOutside(soup0,pivot);
//
//
// assert forall o1 <- soup1, owner1 <- o1.AMFO ::
//    exists o0 <- soup0, owner0 <- o0.AMFO |
//    insidePivot(o1,pivot,owner1) ::  owner1 in flownerAll(soup0);
//

// assert forall owner1 <- flownerAll(soup1) :: exists s0 <- soup0 | owner1 in s0.AMFO ::
//        forall s1 <- soup1 :: (insidePivot(s1,pivot,owner1) ==> insidePivot(s0,pivot,owner1));
//
// assert forall s1 <- soup1, owner1 <- s1.AMFO :: owner1 in flownerAll(soup0);
//
// assert forall s1 <- soup1, owner1 <- s1.AMFO :: owner1 in flownerAll(soup0);


// assert exists s <- soup0, owner1 <- s.AMFO ::



//    assert forall o <- flownerAll(soup1) :: (o in flownerOnlyPivot(soup1,pivot))         ==> (o in flownerOnlyPivot(soup0,pivot));
    // // assert forall o <- flownerAll(soup1) :: (o in flownerExceptPivot(soup1,pivot))       ==> (o in flownerExceptPivot(soup0,pivot));
    // assert forall o <- flownerAll(soup1) :: (o in flownerInsidePivot(soup1,pivot))       ==> (o in flownerInsidePivot(soup0,pivot));
    // assert forall o <- flownerAll(soup1) :: (o in flownerEverythingOutside(soup1,pivot)) ==> (o in flownerEverythingOutside(soup0,pivot));
    // assert forall o <- flownerAll(soup1) :: (o in flownerPivotlyOutside(soup1,pivot))    ==> (o in flownerPivotlyOutside(soup0,pivot));













type FlownerSplit = (Owner, Owner, Owner, Owner, Owner)

predicate flownerSplitOK(soup : OWNR, pivot : Object, split : FlownerSplit)
  requires AllReady(soup) && pivot.Ready()
  {
     var (fAll, fSin, fOut, fPvt, fXpt) := split;

     && (fAll == flownerAll(soup))
     && (fSin == flownerStrictlyInside(soup,pivot))
     && (fOut == flownerFullyOutside(soup,pivot))
     && (fPvt == flownerOnlyPivot(soup,pivot))
     && (fXpt == flownerExceptPivot(soup,pivot))
     && ((fOut + fPvt + fXpt) == flownerEverythingOutside(soup,pivot))
     && ((fOut + fPvt + fXpt) == flownerPivotlyOutside(soup,pivot))
     && (fAll == fSin + fOut + fPvt + fXpt)

     && fSin !! (fOut + fPvt + fXpt)
  }

//  assert fAll == flownerAll(soup);
//  assert fSin == flownerStrictlyInside(soup,pivot);
//  assert fOut == flownerFullyOutside(soup,pivot);
//  assert fPvt == flownerOnlyPivot(soup,pivot);
//  assert fXpt == flownerExceptPivot(soup,pivot);

lemma FLOWNER_ALL_ALL(soup : OWNR, pivot : Object)
 //verified 20 Sep 2026
  requires AllReady(soup) && pivot.Ready()

   ensures flownerAll(soup) == flownerStrictlyInside(soup,pivot) + flownerFullyOutside(soup,pivot) + flownerInsidePivot(soup,pivot)
   ensures flownerInsidePivot(soup,pivot) == (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))

   ensures flownerAll(soup) == flownerStrictlyInside(soup,pivot) +  flownerFullyOutside(soup,pivot) + (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))
   ensures flownerAll(soup) == flownerStrictlyInside(soup,pivot) +  flownerPivotlyOutside(soup,pivot)

   ensures                     flownerStrictlyInside(soup,pivot) !! (flownerFullyOutside(soup,pivot) + flownerInsidePivot(soup,pivot))
   ensures                     flownerStrictlyInside(soup,pivot) !! flownerPivotlyOutside(soup,pivot)
{}


function flownerSplit(os : Owner,pivot : Object) : (rv : FlownerSplit)
  requires AllReady(os) && pivot.Ready()
   ensures flownerSplitOK(os, pivot, rv)
 {
  var fAll := flownerAll(os);
  var fSin := flownerStrictlyInside(os,pivot);
  var fOut := flownerFullyOutside(os,pivot);
  var fPvt := flownerOnlyPivot(os,pivot);
  var fXpt := flownerExceptPivot(os,pivot);
  FLOWNER_ALL_ALL(os,pivot);
  assert fAll == fSin + fOut + fPvt + fXpt;
 (fAll, fSin, fOut, fPvt, fXpt)
 }

function splitThruKlon(soup : OWNR, split : FlownerSplit, m : Klon) : (cc : FlownerSplit)
 //this doesn't acutally jmove the split across the map
 //**it just recaloculates from scratch? */
  requires AllReady(soup) && klonCalid(m)
  requires flownerSplitOK(soup,m.o,split)
  requires m.m.Keys >= soup
   ensures flownerSplitOK(mapThruKlon(soup,m),m.c,cc)
   reads m.hns()
   {
      FLOWNER_ALL_ALL(soup,m.o);

       var (oo_All, oo_Sin, oo_Out, oo_Pvt, oo_Xpt) := split;

       var coup := mapThruKlon(soup,m);
       var pivot := m.c;

       var cc_All : Owner := flownerAll(coup);
       var cc_Sin : Owner := flownerStrictlyInside(coup,pivot);
       var cc_Out : Owner := flownerFullyOutside(coup,pivot);
       var cc_Pvt : Owner := flownerOnlyPivot(coup,pivot);
       var cc_Xpt : Owner := flownerExceptPivot(coup,pivot);

       var cc := (cc_All, cc_Sin, cc_Out, cc_Pvt, cc_Xpt);

       assert cc_All == flownerAll(coup);
       assert cc_Sin == flownerStrictlyInside(coup,pivot);
       assert cc_Out == flownerFullyOutside(coup,pivot);
       assert cc_Pvt == flownerOnlyPivot(coup,pivot);
       assert cc_Xpt == flownerExceptPivot(coup,pivot);

       var cc_FEO := flownerEverythingOutside(coup,pivot);

       var cc_OPX := (cc_Out + cc_Pvt + cc_Xpt);

       assert flownerEverythingOutside(coup,pivot) ==
                    flownerFullyOutside(coup,pivot)
                  + flownerOnlyPivot(coup,pivot)
                  + flownerExceptPivot(coup,pivot)
        by { FLOWNER_EVERYTHING_EVERYWHERE(coup,pivot, cc_FEO, cc_Out, cc_Pvt, cc_Xpt); }


       FLOWNER_EVERYTHING_OUTSIDE(coup,pivot);
       assert cc_OPX == flownerPivotlyOutside(coup,pivot);

       FLOWNER_ALL_EVERYTHING(coup,pivot,cc_All,cc_Sin,cc_Out,cc_Pvt,cc_Xpt);
       assert (cc_All == cc_Sin + cc_Out + cc_Pvt + cc_Xpt);
       assert cc_Sin !! (cc_Out + cc_Pvt + cc_Xpt);

      assert flownerSplitOK(coup,m.c,cc);

      cc
   }

lemma DOUBLE_SPLIT(os : Owner, cs : Owner, os_sp : FlownerSplit, cs_sp : FlownerSplit, m : Klon)
  requires AllReady(os) && AllReady(cs)
  requires klonCalid(m)
  requires m.m.Keys >= os
  requires cs == mapThruKlon(os,m)
  requires flownerSplitOK(os, m.o, os_sp)
  requires flownerSplitOK(cs, m.c, cs_sp)
   ensures os_sp.0 == flownerAll(os)
   ensures cs_sp.0 == flownerAll(cs)
 {
   assert os_sp.1 == flownerStrictlyInside(os,m.o);
   assert cs_sp.1 == flownerStrictlyInside(cs,m.c);
   //FOREST_FOOD(os_sp.1, cs_sp.1, m);
 }


lemma FLOWNER_FLATTEN_TODO_FOR_ALL(soup : OWNR, pivot : Object)
 //verified 21 Sep 2026
  requires AllReady(soup) && pivot.Ready()

   ensures flattenOnlyPivot(soup, pivot) == flownerOnlyPivot(soup, pivot)
   ensures flattenPivotlyOutside(soup, pivot) == flownerPivotlyOutside(soup, pivot)
   ensures flatten(soup) == flownerAll(soup)
{}


lemma FLOWNER_FLATTEN_OnlyPivot(soup : OWNR, pivot : Object)
 //verified 21 Sep 2026
  requires AllReady(soup) && pivot.Ready()

   ensures flattenOnlyPivot(soup, pivot) == flownerOnlyPivot(soup, pivot)
{}

lemma FLOWNER_SHORTCUT_OnlyPivot(soup : OWNR, pivot : Object, rv : Owner)
 //verified 21 Sep 2026
  requires AllReady(soup) && pivot.Ready()

   requires (
              || (rv == flattenOnlyPivot(soup, pivot))
              || (rv == flownerOnlyPivot(soup, pivot))
              || (rv == shortcutOnlyPivot(soup, pivot))
           )

    ensures rv == flattenOnlyPivot(soup, pivot)
    ensures rv == flownerOnlyPivot(soup, pivot)
    ensures rv == shortcutOnlyPivot(soup, pivot)
{
  FLOWNER_FLATTEN_OnlyPivot(soup, pivot);
  LEMMA_shortcutVSflatten2(soup, pivot, shortcutOnlyPivot(soup, pivot), flattenOnlyPivot(soup, pivot));
}


lemma DOUBLE_SPLIT_OnlyPivot(os : Owner, cs : Owner, os_sp : FlownerSplit, cs_sp : FlownerSplit, m : Klon)
 //verified 21Sep2026
  requires AllReady(os) && AllReady(cs)
  requires klonCalid(m)
  requires m.m.Keys >= os
  requires cs == mapThruKlon(os,m)
  requires flownerSplitOK(os, m.o, os_sp)
  requires flownerSplitOK(cs, m.c, cs_sp)
   ensures os_sp.0 == flownerAll(os)
   ensures cs_sp.0 == flownerAll(cs)
   ensures os_sp.3 == flownerOnlyPivot(os, m.o)
   ensures cs_sp.3 == flownerOnlyPivot(cs, m.c)

   ensures (m.o  in os_sp.0) ==> (os_sp.3 == m.o.AMFO)
   ensures (m.o !in os_sp.0) ==> (os_sp.3 == {})
   ensures (m.o  in os_sp.0) ==> (cs_sp.3 == m.c.AMFO)
   ensures (m.o !in os_sp.0) ==> (cs_sp.3 == {})

//   ensures os_sp.3 == (if (m.o in os_sp.0) then (m.o.AMFO) else {})
 {
   assert os_sp.3 == flownerOnlyPivot(os, m.o);
FLOWNER_SHORTCUT_OnlyPivot(os, m.o, os_sp.3);
   assert os_sp.3 == shortcutOnlyPivot(os, m.o);
 LEMMA_shortcutOnlyPivot1(os, m.o, os_sp.3);

   assert (m.o  in os_sp.0) ==> (os_sp.3 == m.o.AMFO);
   assert (m.o !in os_sp.0) ==> (os_sp.3 == {});
   if (m.o in os_sp.0) { assert os_sp.3 == m.o.AMFO; } else { assert os_sp.3 == {}; }
//   assert os_sp.3 == (if (m.o in os_sp.0) then (m.o.AMFO) else {});

  assert (m.o in os_sp.0) ==> (m.c in cs_sp.0);

   assert cs_sp.3 == flownerOnlyPivot(cs, m.c);
FLOWNER_SHORTCUT_OnlyPivot(cs, m.c, cs_sp.3);
   assert cs_sp.3 == shortcutOnlyPivot(cs, m.c);
 LEMMA_shortcutOnlyPivot1(cs, m.c, cs_sp.3);

 }



lemma SIDEWAYS_StrictlyInside(soup0 : Owner, soup1 : Owner, f0 : Owner, f1 : Owner, m : Klon)
//one more attempt at the "inside problem"
  requires AllReady(soup0) && AllReady(soup1)
  requires klonCalid(m)
  requires m.m.Keys >= soup0
  requires soup1 == mapThruKlon(soup0, m)
  requires f0 == flownerStrictlyInside(soup0, m.o)
  requires f1 == flownerStrictlyInside(soup1, m.c)
//   ensures forall f <- f0 :: m.m[f] in f1
{
  assert f1 <= flownerAll(soup1);
  assert f1 == flownerStrictlyInside(soup1, m.c);
  FLOWNER_FLATTEN_StrictlyInside(soup1,m.c);
  assert f1 == flattenStrictlyInside(soup1, m.c);
  assert f1 == (set x <- flatten(soup1) | strictlyInside(x,m.c));
  assert forall f <- f1 :: strictlyInside(f,m.c);
  assert f1 == (set x <- flatten(mapThruKlon(soup0, m)) | strictlyInside(x,m.c));
  assert f1 == (set x <- flatten(set s <- soup0 :: m.m[s]) | strictlyInside(x,m.c));
  assert m.c == m.m[m.o];
//  assert f1 == (set x <- flatten(set s <- soup0 | strictlyInside(s,m.o) :: m.m[s]));

  assert forall f <- f0 :: strictlyInside(f,m.o) <==>  strictlyInside(m.m[f],m.m[m.o]);


//   assert f0 == flownerStrictlyInside(soup0, m.o);
//   FLOWNER_FLATTEN_StrictlyInside(soup0,m.o);
//   assert f0 == flattenStrictlyInside(soup0, m.o);
//   assert f0 == (set x <- flatten(soup0) | strictlyInside(x,m.o));
//   assert forall f <- f0 :: strictlyInside(f,m.o);
//
//
//   assert f1 == flattenStrictlyInside(mapThruKlon(soup0, m), m.c);

}


lemma MAP_THRU_KLON_FILTER(soup : Owner, m : Klon)
//one more attempt at the "inside problem"
  requires AllReady(soup)
  requires klonCalid(m)
  requires m.m.Keys >= soup
  //  ensures (set c <- mapThruKlon(soup,m) | strictlyInside(c,m.c))
  //    == mapThruKlon((set s <- soup | strictlyInside(s,m.o)),m)
   {
    var sf := (set s <- soup | strictlyInside(s,m.o) :: s);
    var f  := mapThruKlon(sf,m);
    assert f == (set s <- sf :: m.m[s]);
    assert f == (set s <- (set s <- soup | strictlyInside(s,m.o) :: s) :: m.m[s]);

    assert f == (set s <- soup | strictlyInside(s,m.o) :: m.m[s]);
    assert f == (set s <- soup | strictlyInside(s,m.o) :: m.m[s]);
//    assert f == (set s <- (set s <- soup :: m.m[s]) | strictlyInside(s,m.o) :: s);
//james wonders if this is the "set comprehension problem"
//and if so, can he find rhe code from TRUMP or LUXON that likely fixes it?
//    assert f == (set c <- (set s <- soup :: m.m[s]) | strictlyInside(c,m.m[m.o]) :: c);


  //  assert f ==  mapThruKlon(  (set s <- soup | strictlyInside(s,m.o) :: s), m);

//    assert f ==  (set s <- mapThruKlon(soup,m) | strictlyInside(s,m.m[m.o]) :: s);
//    assert f ==  (set s <- mapThruKlon(soup,m) | strictlyInside(s,m.c) :: s);
   }

lemma FLOWNER_FLATTEN_StrictlyInside(soup : OWNR, pivot : Object)
  requires AllReady(soup) && pivot.Ready()
   ensures flattenStrictlyInside(soup, pivot) == flownerStrictlyInside(soup, pivot)
   ensures flownerStrictlyInside(soup, pivot) <= flownerAll(soup)
{}


lemma DOUBLE_SPLIT_StrictlyInside(os : Owner, cs : Owner, os_sp : FlownerSplit, cs_sp : FlownerSplit, m : Klon)
  requires AllReady(os) && AllReady(cs)
  requires klonCalid(m)
  requires m.m.Keys >= os
  requires cs == mapThruKlon(os,m)
  requires flownerSplitOK(os, m.o, os_sp)
  requires flownerSplitOK(cs, m.c, cs_sp)
   ensures os_sp.0 == flownerAll(os)
   ensures cs_sp.0 == flownerAll(cs)
   ensures os_sp.1 == flownerStrictlyInside(os, m.o)
   ensures cs_sp.1 == flownerStrictlyInside(cs, m.c)

  //  ensures forall o <- os_sp.1 :: (
  //     && (o in m.m.Keys)
  //     && (strictlyInside(o,m.o))
  //     && (klonLine(o,m.m[o],m))
  //     && (m.m[o] in cs_sp.1)
  // )

 {
   assert os_sp.1 == flownerStrictlyInside(os,m.o);
   assert cs_sp.1 == flownerStrictlyInside(cs,m.c);

   assert m.m.Keys >= os_sp.1;

   assert forall o <- os_sp.1 ::
//    && (exists s <- os :: ownerStrictlyInside(s,m.o,o))
    (var c := m.m[o];
        && (strictlyInside(o,m.o))
    );

   assert forall o <- os_sp.1 ::
    (var c := m.m[o];
        && (klonLine(o,c,m))
    );

   assert forall o <- os_sp.1 ::
    (var c := m.m[o];
        && (klonIdentity(o,c,m))
        && (o != c)
        && (strictlyInside(c,m.c))
   );

  assert cs_sp.1 <= cs_sp.0;

  //     assert forall o <- os_sp.1 :: //Err
  //   (var c := m.m[o];
  //       && (c in cs_sp.0)
  //  );

  //     assert forall o <- os_sp.1 ::   //Err
  //   (var c := m.m[o];
  //       && (c in cs_sp.1)
  //  );


 }




lemma ORIGINAL_ALL_OBJECTS_OUTSIDE_MAP(os : Owner, m : Klon)
  requires AllReady(os)
  requires klonCalid(m)
  requires os <= m.m.Keys
  requires forall o <- os :: outside(o,m.o)

   ensures outside(m.o,m.c)
   ensures forall o <- os :: m.m[o] == o
   ensures forall o <- os :: outside(o,m.c)
   ensures mapThruKlon(os,m) == os
   ensures flownerPivotlyOutside(os,m.o) == flownerAll(os)
   ensures flownerPivotlyOutside(os,m.c) == flownerAll(os)
   ensures flownerPivotlyOutside(mapThruKlon(os,m),m.c) == flownerAll(os)
   ensures flownerPivotlyOutside(os,m.o) == flownerPivotlyOutside(mapThruKlon(os,m),m.c)

   {
    var fPO := flownerPivotlyOutside(os,m.o);

    FLOWNER_FLATTEN_TODO_FOR_ALL(os,m.o);
    FLOWNER_FLATTEN_TODO_FOR_ALL(os,m.c);

    assert flownerPivotlyOutside(os,m.o) == flownerAll(os);
    assert flownerPivotlyOutside(os,m.c) == flownerAll(os);
    assert flownerPivotlyOutside(mapThruKlon(os,m),m.c) == flownerAll(os);


   }

lemma MAP_OBJECTS_OUTSIDE(os : Owner, oos : Owner, m : Klon)
  requires AllReady(os)
  requires klonCalid(m)
  requires os <= m.m.Keys
  requires oos == (set o <- os | outside(o,m.o))  //<==BINARY VERSION

//  HMM.  grr.
//lthinkg about this through 
//gblahy

///MNOST LIKEKY this shouljd be tqeaked to take an input a soup (or two)
//and then produce the sets of outsidee thingus
//and then dio the analysis on them....
//for flownerPivotlyOutside we can rediret through flowerAll()/flattenX
//hmm. or perhaps that won't relaly work
//in whcih case can we get at the ternary version of the binary version here
//and yet get to the same place...?

///ALSO look hard at FLOWER_SPLIT_H around line 1420
//if I can get flownerFullyOutside going  --FLOWER_JOIN_All
//whcih frankly should be more than enuf
//then isn't that IT?
//are we ALREADY FUCKING THERE?????



   ensures outside(m.o,m.c)
   ensures forall o <- oos :: m.m[o] == o
   ensures mapThruKlon(oos,m) == oos
   ensures flownerPivotlyOutside(oos,m.o) == flownerAll(oos)
   ensures flownerPivotlyOutside(oos,m.c) == flownerAll(oos)
   ensures flownerPivotlyOutside(mapThruKlon(oos,m),m.c) == flownerAll(oos)
   {
    var fPO := flownerPivotlyOutside(oos,m.o);

    FLOWNER_FLATTEN_TODO_FOR_ALL(oos,m.o);
    FLOWNER_FLATTEN_TODO_FOR_ALL(oos,m.c);

    assert flownerPivotlyOutside(oos,m.o) == flownerAll(oos);
    assert flownerPivotlyOutside(oos,m.c) == flownerAll(oos);
    assert flownerPivotlyOutside(mapThruKlon(oos,m),m.c) == flownerAll(oos);
   }

// lemma FLOWNER_PIVOTLY_OUTSIDE(os : Owner, m : Klon)
//   requires AllReady(os)
//   requires klonCalid(m)
//   requires os <= m.m.Keys
//   requires forall o <- os :: outside(o,m.o)
//    ensures flattenPivotlyOutside(os,m) == os
//   {
//     assert pivotlyOutside(os,m.o) <== outside(os,m.o);
//     (set x <- flatten(soup) | pivotlyOutside(x,pivot));
//     assert flattenPivotlyOutside(os,m) == (set x <- flatten(soup) | pivotlyOutside(x,pivot));
//   }


lemma ONE_OBJECT_OUTSIDE(o : Object, c : Object, m : Klon)
  //verifies 21Sep2026
  requires o.Ready() && c.Ready()
  requires klonCalid(m)
  requires o in m.m.Keys
  requires m.m[o] == c
  requires outside(o,m.o)

   ensures {c} == mapThruKlon({o},m)
   ensures outside(c,m.c)
   ensures o == c
{
  assert klonLine(o,c,m);
  assert klonIdentity(o,c,m);
  assert outside(o,m.o);

  MAPPEN_ONE(o,m);
}


lemma MAPPEN_ONE(o : Object, m : Klon)
 //took at least an hour trying more sensile versions of the next 12 lines
 //to just copy these ones in from an earlier file because they work.
  requires o.Ready()
  requires o in m.m.Keys
  requires klonReady(m)
  requires klonCalid(m)
  ensures mapThruKlon({o},m) == {m.m[o]}
{
 FLATTEN_ONE(o);
}
lemma FLATTEN_ONE(o : Object)
  requires o.Ready()
  ensures flatten({o}) == {o} + flatten(o.owner) == o.AMFO
{}


lemma flownerFullyOutside_OUTSIDE(os : Owner, FFO : Owner, pivot : Object)
//verified 22 sept
  requires AllReady(os)
  requires AllReady(FFO)
  requires pivot.Ready()
  requires FFO == flownerFullyOutside(os, pivot)
   ensures forall f <- FFO :: outside(f,pivot)
{}

lemma flownerExceptPivot_OUTSIDE(os : Owner, FEP : Owner, pivot : Object)
   //verified 22 sept
  requires AllReady(os)
  requires AllReady(FEP)
  requires pivot.Ready()
  requires FEP == flownerExceptPivot(os, pivot)
   ensures forall f <- FEP :: outside(f,pivot)
{}



lemma DOUBLE_SPLIT_Outside(os : Owner, cs : Owner, os_sp : FlownerSplit, cs_sp : FlownerSplit, m : Klon)
 //verified 21Sep2026  (well; kinda)  --- except the last two crucial ensures below
  requires AllReady(os) && AllReady(cs)
  requires klonCalid(m)
  requires m.m.Keys >= os
  requires cs == mapThruKlon(os,m)
  requires flownerSplitOK(os, m.o, os_sp)
  requires flownerSplitOK(cs, m.c, cs_sp)
   ensures os_sp.0 == flownerAll(os)
   ensures cs_sp.0 == flownerAll(cs)
   ensures os_sp.2 == flownerFullyOutside(os, m.o)
   ensures cs_sp.2 == flownerFullyOutside(cs, m.c)
   ensures os_sp.4 == flownerExceptPivot(os, m.o)
   ensures cs_sp.4 == flownerExceptPivot(cs, m.c)

   ensures os_sp.2 == cs_sp.2   //ERR
   ensures os_sp.4 == cs_sp.4   //ERR
{
   assert m.m.Keys >= os_sp.2;
   assert m.m.Keys >= os_sp.4;

   flownerFullyOutside_OUTSIDE(os, os_sp.2, m.o);
   flownerFullyOutside_OUTSIDE(cs, cs_sp.2, m.c);
   flownerExceptPivot_OUTSIDE(os, os_sp.4, m.o);
   flownerExceptPivot_OUTSIDE(cs, cs_sp.4, m.c);

}

//    assert os_sp.2 == flownerFullyOutside(os, m.o);
//    assert cs_sp.2 == flownerFullyOutside(cs, m.c);
//    assert cs_sp.2 == flownerFullyOutside(mapThruKlon(os,m), m.c);
//
//    var oos := (set o <- os | outside(o,m.o));
//    MAP_OBJECTS_OUTSIDE(os,oos,m);


//
//    ensures forall o <- os :: outside(o,m.c)
//    ensures mapThruKlon(os,m) == os
//    ensures flownerPivotlyOutside(os,m.o) == flownerAll(os)
//    ensures flownerPivotlyOutside(os,m.c) == flownerAll(os)
//    ensures flownerPivotlyOutside(mapThruKlon(os,m),m.c) == flownerAll(os)
//
//    assert forall k <- os_sp.2 :: klonLine(k,m.m[k],m);
//    assert forall k <- os_sp.2 :: outside(k,m.o);
//    assert forall k <- os_sp.2 :: outside(m.m[k],m.c);
//    assert forall k <- os_sp.2 :: k == m.m[k];
//
//    assert forall v <- cs_sp.2 :: klonLine(v,m.m[v],m);
//    assert forall v <- cs_sp.2 :: outside(v,m.c);
//    assert forall v <- cs_sp.2 :: outside(v,m.o);
//    assert forall v <- cs_sp.2 :: v == m.m[v];
//
//    assert forall k <- os_sp.2 :: k in m.m.Keys;
//    assert forall k <- os_sp.2 :: k in m.m.Values;
//
//    assert forall v <- cs_sp.2 :: v in m.m.Values;
//    assert forall v <- cs_sp.2 :: v in m.m.Keys;
//
//
//    assert cs == mapThruKlon(os,m);
//
//    assert forall o <- os_sp.2 :: m.m[o] in cs_sp.2;
//    assert forall c <- cs_sp.2 :: c in cs_sp.2;
//
//    assert os_sp.2 >= cs_sp.2;
//    assert os_sp.2 <= cs_sp.2;
//    assert os_sp.2 == cs_sp.2;
//
// }

//    ORIGINAL_ALL_OBJECTS_OUTSIDE_MAP(os_sp.2, m);
//    assert flownerPivotlyOutside(os_sp.2,m.o) == flownerPivotlyOutside(mapThruKlon(os_sp.2,m),m.c);
//
//    assert flownerPivotlyOutside(os_sp.2,m.o) >= flownerFullyOutside(os_sp.2,m.o);
//    assert flownerPivotlyOutside(mapThruKlon(os_sp.2,m),m.o) >= flownerFullyOutside(mapThruKlon(os_sp.2,m),m.o);
//
//    forall x <- flownerPivotlyOutside(os_sp.2,m.o) ensures (true)
//     {
//       assert x in flownerPivotlyOutside(mapThruKlon(os_sp.2,m),m.c);
//       assert (x in flownerFullyOutside(os_sp.2,m.o))  ==> (x in flownerFullyOutside(mapThruKlon(os_sp.2,m),m.o));
//       assert (x in flownerFullyOutside(os_sp.2,m.o)) <==  (x in flownerFullyOutside(mapThruKlon(os_sp.2,m),m.o));
//       assert (x in flownerFullyOutside(os_sp.2,m.o)) <==> (x in flownerFullyOutside(mapThruKlon(os_sp.2,m),m.o));
//     }
//
//    assert flownerFullyOutside(os_sp.2,m.o) == flownerFullyOutside(mapThruKlon(os_sp.2,m),m.c);
//
//    assert flownerPivotlyOutside(os_sp.2,m.o) == flownerPivotlyOutside(cs_sp.2,m.c);
//    assert os_sp.2 == cs_sp.2;



  //  assert os_sp.2 >= cs_sp.2;
  //  assert forall v <- cs_sp.2 :: v in  os_sp.2;
//    assert forall k <- os_sp.2 :: k in  cs_sp.2;
//
//    forall k <- os_sp.2 ensures (true) //by
//     {
//       ONE_OBJECT_OUTSIDE(k,m.m[k],m);
//     //  assert k in cs_sp.2;
//     }

lemma KRX(k : Object, m : Klon)
  requires klonCalid(m)
   ensures outside(m.o,m.c)
   ensures forall x <- m.m.Keys | outside(x,m.o) :: outside(x,m.c)
{}



lemma XLR(x : Owner, l : Owner, r : Owner, m : Klon)
  requires AllReady(x)
  requires AllReady(l)
  requires AllReady(r)
  requires klonCalid(m)
  requires x <= m.m.Keys
  requires l == flownerPivotlyOutside(x, m.o)
  requires r == flownerPivotlyOutside(mapThruKlon(x, m), m.c)

  // ensures outside(m.o,m.c)
  ensures l == r
  {
   flownerFullyOutside_OUTSIDE(x, l, m.o);
   flownerFullyOutside_OUTSIDE(mapThruKlon(x, m), r, m.c);

   assert forall l1 <- l :: (
     var r1 := m.m[l1];
     && (klonLine(l1,r1,m))
     && (outside(l1,m.o) && outside(r1,m.c))
     && (klonIdentity(l1,r1,m))
     && (l1 == r1)

   );


  //  assert outside(m.o,m.c);
  //  flownerFullyOutside_OUTSIDE(mapThruKlon(x, m), r, m.o);  //ERR

   assert flownerFullyOutside(x, m.o) ==
      (set o <- x, owner <- o.AMFO
        | PART_INSIDE_OWNER(x,m.o); ownerFullyOutside(o,m.o,owner) :: owner);
  }

lemma FLOWER_SPLIT_H(oo : Owner, ob : Bound, pivot : Object)
 //given Foo >= Fob, then the vartious components are >=
 //should be xo & xb??
  requires AllReady(oo)
  requires AllReady(ob)
  requires pivot.Ready()
  requires flatten(oo) >= flatten(ob) ///works better than flownerALl. why?
//  requires flownerAll(oo) >= flownerAll(ob)
   ensures flownerStrictlyInside(oo,pivot) >= flownerStrictlyInside(ob,pivot)
   ensures flownerOnlyPivot(oo,pivot) >= flownerOnlyPivot(ob,pivot)
  //  ensures flownerExceptPivot(oo,pivot) >= flownerExceptPivot(ob,pivot)
   ensures flownerInsidePivot(oo,pivot) >= flownerInsidePivot(ob,pivot)
// ensures flownerFullyOutside(oo,pivot) >= flownerFullyOutside(ob,pivot)

//    ensures (flownerInsidePivot(oo,pivot) + flownerStrictlyInside(oo,pivot) + flownerFullyOutside(oo,pivot))
//       >= (flownerInsidePivot(ob,pivot) + flownerStrictlyInside(ob,pivot) + flownerFullyOutside(ob,pivot))
//
//    ensures (flownerInsidePivot(oo,pivot) + flownerFullyOutside(oo,pivot))
//       >= (flownerInsidePivot(ob,pivot) + flownerFullyOutside(ob,pivot))

   ensures flownerEverythingOutside(oo,pivot) >= flownerEverythingOutside(ob,pivot)

  {
     FLOWNER_DISJOINT(oo, pivot);
     FLOWNER_DISJOINT(ob, pivot);



  //  ensures flownerStrictlyInside(soup,pivot) !! flownerOnlyPivot(soup,pivot)
  //  ensures flownerStrictlyInside(soup,pivot) !! flownerExceptPivot(soup,pivot)
  //  ensures flownerStrictlyInside(soup,pivot) !! flownerFullyOutside(soup,pivot)
  //  ensures flownerStrictlyInside(soup,pivot) !! (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot) + flownerFullyOutside(soup,pivot))
  //  ensures (flownerOnlyPivot(soup,pivot) !! flownerExceptPivot(soup,pivot))
  }



lemma FLOWER_JOIN_InsidePivot(oo : Owner, ob : Bound, pivot : Object)
  requires AllReady(oo)
  requires AllReady(ob)
  requires pivot.Ready()

  requires flownerOnlyPivot(oo,pivot) >= flownerOnlyPivot(ob,pivot)
  requires flownerExceptPivot(oo,pivot) >= flownerExceptPivot(ob,pivot)

   ensures flownerInsidePivot(oo,pivot) == flownerOnlyPivot(oo,pivot) + flownerExceptPivot(oo,pivot)
   ensures flownerInsidePivot(ob,pivot) == flownerOnlyPivot(ob,pivot) + flownerExceptPivot(ob,pivot)
   ensures flownerInsidePivot(oo,pivot) >= flownerInsidePivot(ob,pivot)
   {}


lemma FUCKED(o0 : Owner, o1 : Owner, o2 : Owner, b0 : Owner, b1 : Owner, b2 : Owner)
  //set >= monotonic over disjoint splts and through joint sum
  requires o0 >= b0
  requires (o1+o2) >= (b1+b2)
  requires o0 !! (o1+o2)
  requires b0 !! (b1+b2)
   ensures (o0+o1+o2) >= (b0+b1+b2)
   {}


lemma FUCK4D(o0 : Owner, o1 : Owner, o2 : Owner, o3 : Owner, b0 : Owner, b1 : Owner, b2 : Owner, b3 : Owner)
  //set >= monotonic over disjoint splts and through joint sum
  requires o0 >= b0
  requires (o1+o2+o3) >= (b1+b2+b3)
  requires o0 !! (o1+o2+o3)
  requires b0 !! (b1+b2+b3)
   ensures (o0+o1+o2+o3) >= (b0+b1+b2+b3)
   {}

lemma UNFUCK4D(o0 : Owner, o1 : Owner, o2 : Owner, o3 : Owner, b0 : Owner, b1 : Owner, b2 : Owner, b3 : Owner)
  //set >= monotonic over disjoint splts and through joint sum
  requires (o0 + b0) !! ((o1+o2+o3) + (b1+b2+b3))
  requires (o0+o1+o2+o3) >= (b0+b1+b2+b3)
   ensures o0 >= b0
   ensures (o1+o2+o3) >= (b1+b2+b3)
   {
      //SET_DISJOINT_GT(o0, (o1+o2+o3), b0, (b1+b2+b3));
   }


lemma SET_DISJOINT_GT(o0 : Owner, o1 : Owner, b0 : Owner, b1 : Owner)
  //set >= monotonic over disjoint splts
  requires (o0 + b0) !! (o1 + b1)
  //  ensures ((o0+o1) >= (b0+b1))  ==> ((o0 >= b0) && (o1 >= b1))
  //  ensures ((o0+o1) >= (b0+b1)) <==  ((o0 >= b0) && (o1 >= b1))
   ensures ((o0+o1) >= (b0+b1)) <==> ((o0 >= b0) && (o1 >= b1))
   {}





lemma FLOWER_JOIN_All(oo : Owner, ob : Bound, pivot : Object)
 //given the vartious components are >=, conclude Foo >= Fob,
 //just a nice? version of FLOWER_JOIN_H without the typo
  requires AllReady(oo)
  requires AllReady(ob)
  requires pivot.Ready()

  requires flownerStrictlyInside(oo,pivot) >= flownerStrictlyInside(ob,pivot)
  requires (flownerInsidePivot(oo,pivot) + flownerFullyOutside(oo,pivot)) >= (flownerInsidePivot(ob,pivot) + flownerFullyOutside(ob,pivot))

   ensures flownerStrictlyInside(oo,pivot) + (flownerInsidePivot(oo,pivot) + flownerFullyOutside(oo,pivot)) >=
           flownerStrictlyInside(ob,pivot) + (flownerInsidePivot(ob,pivot) + flownerFullyOutside(ob,pivot))

   ensures flownerAll(oo) == flownerStrictlyInside(oo,pivot) + (flownerInsidePivot(oo,pivot) + flownerFullyOutside(oo,pivot))
   ensures flownerAll(ob) == flownerStrictlyInside(ob,pivot) + (flownerInsidePivot(ob,pivot) + flownerFullyOutside(ob,pivot))
   ensures flownerAll(oo) >= flownerAll(ob)
   {
    FUCKED(flownerStrictlyInside(oo,pivot), flownerInsidePivot(oo,pivot), flownerFullyOutside(oo,pivot),
           flownerStrictlyInside(ob,pivot), flownerInsidePivot(ob,pivot), flownerFullyOutside(ob,pivot)) ;
    FLOWNER_DISJOINT(oo, pivot);
    FLOWNER_DISJOINT(ob, pivot);
    FLOWNER_ALL_ALL(oo,pivot);
    FLOWNER_ALL_ALL(ob,pivot);
   }

lemma FLOWER_JOIN_H(oo : Owner, ob : Bound, pivot : Object)
 //given the vartious components are >=, conclude Foo >= Fob,
 //should be xo & xb??
  requires AllReady(oo)
  requires AllReady(ob)
  requires pivot.Ready()

  requires flownerStrictlyInside(oo,pivot) >= flownerStrictlyInside(ob,pivot)

  requires flownerOnlyPivot(oo,pivot) >= flownerOnlyPivot(ob,pivot)
  requires flownerExceptPivot(oo,pivot) >= flownerExceptPivot(ob,pivot)

  requires flownerFullyOutside(oo,pivot) >= flownerFullyOutside(ob,pivot)

  requires flownerEverythingOutside(oo,pivot) >= flownerEverythingOutside(ob,pivot)

   ensures (flownerInsidePivot(oo,pivot) + flownerFullyOutside(oo,pivot)) >= (flownerInsidePivot(ob,pivot) + flownerFullyOutside(ob,pivot))

   ensures flownerInsidePivot(oo,pivot) >= flownerInsidePivot(ob,pivot)


  //  ensures (flownerInsidePivot(oo,pivot) + flownerFullyOutside(oo,pivot))
  //     >= (flownerInsidePivot(ob,pivot) + flownerFullyOutside(ob,pivot))


   ensures (flownerInsidePivot(oo,pivot) + flownerStrictlyInside(oo,pivot) + flownerFullyOutside(oo,pivot))
      >= (flownerInsidePivot(ob,pivot) + flownerStrictlyInside(ob,pivot) + flownerFullyOutside(ob,pivot))

   ensures flownerAll(oo) == flownerStrictlyInside(oo,pivot) + flownerEverythingOutside(oo,pivot)
   ensures flownerAll(ob) == flownerStrictlyInside(ob,pivot) + flownerEverythingOutside(ob,pivot)

   ensures flownerAll(oo) == flownerStrictlyInside(oo,pivot) + flownerFullyOutside(oo,pivot) + flownerInsidePivot(oo,pivot)
   ensures flownerAll(ob) == flownerStrictlyInside(ob,pivot) + flownerFullyOutside(ob,pivot) + flownerInsidePivot(ob,pivot)
   ensures flownerAll(oo) >= flownerAll(ob)
  {
        FUCKED(flownerStrictlyInside(oo,pivot), flownerInsidePivot(oo,pivot), flownerFullyOutside(oo,pivot),
           flownerStrictlyInside(ob,pivot), flownerInsidePivot(ob,pivot), flownerFullyOutside(ob,pivot)) ;
    FLOWNER_DISJOINT(oo, pivot);
    FLOWNER_DISJOINT(ob, pivot);
    FLOWNER_ALL_ALL(oo,pivot);
    FLOWNER_ALL_ALL(ob,pivot);
  }


//shpudl thje next three be turned into predicates,
//one for each case of klonIdentity?  OH probably but fuck it
lemma WOOD_FOOD(o : Object, c : Object, m : Klon)
 //expands on some consequences of klonLine(o,c) when o is *strictlyInside*
 //that inside objects are 1:1 with the clone
 //and also that their owners are -thus the strictlyInside
 //
 //is the is the point about owners (or boundS) thje important one?
   requires o.Ready()
   requires c.Ready()
   requires klonCalid(m)


   requires o in m.m.Keys
   requires strictlyInside(o,m.o)
   requires c == m.m[o]

    ensures klonLine(o,c,m)
    ensures klonGeometry(o,c,m)
    ensures klonIdentity(o,c,m)
    ensures (o != m.o) && (not(outside(o,m.o)))
    ensures strictlyInside(c,m.c)
    ensures (o != m.o) && (o != c)
    ensures (c.owner == mapThruKlon(o.owner, m))
    ensures (c.bound == mapThruKlon(o.bound, m))

    ensures woodFood(o,c,m)
{}

predicate woodFood(o : Object, c : Object, m : Klon)
   requires o.Ready()
   requires c.Ready()
   requires klonCalid(m)

   requires o in m.m.Keys
   requires strictlyInside(o, m.o)
   requires c == m.m[o]

   reads m.hns()
{
    && klonLine(o,c,m)
    && klonGeometry(o,c,m)
    && klonIdentity(o,c,m)
    && strictlyInside(c,m.c)
    && (o != c)
    && (c.owner == mapThruKlon(o.owner, m))
    && (c.bound == mapThruKlon(o.bound, m))
}





lemma WOOD_TRAP(o : Object, c : Object, m : Klon)
 //expands on some consequences of klonLine(o,c) when o is *pivot*
 //
 //is the is the point about owners (or boundS) thje important one?
   requires o.Ready()
   requires c.Ready()
   requires klonCalid(m)

   requires o in m.m.Keys
   requires o == m.o
   requires c == m.m[o]

    ensures klonLine(o,c,m)
    ensures klonGeometry(o,c,m)
    ensures klonIdentity(o,c,m)
    ensures c == m.c
    ensures c.owner == m.c.owner == m.clowner
    ensures c.bound == m.c.bound == m.clbound

    ensures woodTrap(o,c,m)
{}


predicate woodTrap(o : Object, c : Object, m : Klon)
   requires o.Ready()
   requires c.Ready()
   requires klonCalid(m)

   requires o in m.m.Keys
   requires o == m.o
   requires c == m.m[o]

   reads m.hns()
{
    && klonLine(o,c,m)
    && klonGeometry(o,c,m)
    && klonIdentity(o,c,m)
    && c == m.c
    && c.owner == m.c.owner == m.clowner
    && c.bound == m.c.bound == m.clbound
}



lemma WOOD_REAL(o : Object, c : Object, m : Klon)
 //expands on some consequences of klonLine(o,c) when o is *outside* the pivot
 //
 //is the is the point about owners (or boundS) thje important one?
   requires o.Ready()
   requires c.Ready()
   requires klonCalid(m)

   requires o in m.m.Keys
   requires outside(o, m.o)
   requires c == m.m[o]

    ensures klonLine(o,c,m)
    ensures klonGeometry(o,c,m)
    ensures klonIdentity(o,c,m)
    ensures c == o != m.o
    ensures c.owner == o.owner
    ensures c.bound == o.bound

    ensures woodReal(o,c,m)
{}

predicate woodReal(o : Object, c : Object, m : Klon)
   requires o.Ready()
   requires c.Ready()
   requires klonCalid(m)

   requires o in m.m.Keys
   requires outside(o, m.o)
   requires c == m.m[o]

   reads m.hns()
{
    && klonLine(o,c,m)
    && klonGeometry(o,c,m)
    && klonIdentity(o,c,m)
    && c == o != m.o
    && c.owner == o.owner
    && c.bound == o.bound
}


lemma FOREST_REAL(os : Owner, cs : Owner, m : Klon)
   //lifts WOOD_REAL to FOREST - verifies on lately with nothing in the body...? 38s
   requires AllReady(os)
   requires AllReady(cs)
   requires klonCalid(m)

   requires os <= m.m.Keys
   requires forall o <- os :: outside(o, m.o)
   requires cs == mapThruKlon(os,m)

    ensures forall o <- os :: klonLine(o,m.m[o],m)
    ensures forall o <- os :: klonGeometry(o,m.m[o],m)
    ensures forall o <- os :: klonIdentity(o,m.m[o],m)
    ensures forall o <- os :: m.m[o] == o != m.o
    ensures forall o <- os :: m.m[o].owner == o.owner
    ensures forall o <- os :: m.m[o].bound == o.bound

    ensures forall o <- os :: woodReal(o,m.m[o],m)
{
forall o <- os ensures (woodReal(o,m.m[o],m)) //by
 {
  WOOD_REAL(o,m.m[o],m);
 }
}

//DUNNO IF THERE FOREST STUFF is RIGHT
//GRR. should it dwepend on :  cs == mapThruKlon(os,m)
//***or is that what it needs to be finding??***
//      WOOD_FOOD(o,m.m[o],m);

lemma FOREST_FOOD(os : Owner, cs : Owner, m : Klon)
    // arguments should really be: os_Sin, cs_Sin
   //lifts WOOD_FOOD to FOREST - verifies on lately with nothing in the body...? 38s
   requires AllReady(os)
   requires AllReady(cs)
   requires klonCalid(m)

   requires os <= m.m.Keys
   requires forall o <- os :: strictlyInside(o, m.o)
   requires cs == mapThruKlon(os,m)

    ensures forall o <- os :: klonLine(o,m.m[o],m)
    ensures forall o <- os :: klonGeometry(o,m.m[o],m)
    ensures forall o <- os :: klonIdentity(o,m.m[o],m)
    ensures forall o <- os :: strictlyInside(m.m[o],m.c) && (o != m.m[o])
    ensures forall o <- os :: m.m[o].owner == mapThruKlon(o.owner, m)
    ensures forall o <- os :: m.m[o].bound == mapThruKlon(o.bound, m)

    ensures forall o <- os :: woodFood(o,m.m[o],m)
{
forall o <- os ensures (woodFood(o,m.m[o],m)) //by
 {
  WOOD_FOOD(o,m.m[o],m);
 }

}



lemma FLOWER_POWER_V_strictlyInside(ox : Owner, cx : Owner, m : Klon)
  requires AllReady(ox)
  requires AllReady(cx)
  requires klonCalid(m)
  requires m.m.Keys >= ox
  requires cx == mapThruKlon(ox, m)
//   ensures forall i <- flownerStrictlyInside(ox,m.o) :: m.m[i] in flownerStrictlyInside(cx,m.c)
//   ensures forall o <- flownerFullyOutside(ox,m.o)   :: (o == m.m[o]) && (m.m[o] in flownerFullyOutside(cx,m.c))

  {
    assert forall i <- flownerStrictlyInside(ox,m.o) :: (i in flownerAll(ox));
    assert forall i <- flownerStrictlyInside(ox,m.o) :: strictlyInside(i,m.o);
    assert forall i <- flownerAll(ox) | strictlyInside(i,m.o) :: i in flownerStrictlyInside(ox,m.o);
    assert forall i <- flownerStrictlyInside(ox,m.o) :: i in m.m.Keys;
    assert forall i <- flownerStrictlyInside(ox,m.o) :: klonLine(i,m.m[i],m);

    forall o <- ox, owner <- o.AMFO | ownerStrictlyInside(o,m.o,owner)
        ensures (true) //by
///        ensures (ownerStrictlyInside(m.m[o],m.c,m.m[owner])) //by
     {
        assert strictlyInside(o,m.o);
        assert strictlyInside(owner,m.o);
        var c := m.m[o];
        var cowner := m.m[owner];

        WOOD_FOOD(o,c,m);
        // assert klonLine(o,c,m);
        // assert klonGeometry(o,c,m);
        // assert klonIdentity(o,c,m);
        // assert (o != m.o) && (not(outside(o,m.o)));
        // assert strictlyInside(c,m.c);
        // assert (o != m.o) && (o != c);
        // assert (c.owner == mapThruKlon(o.owner, m));
        // assert (c.bound == mapThruKlon(o.bound, m));

        WOOD_FOOD(owner,cowner,m);
        // assert klonLine(owner,cowner,m);
        // assert klonGeometry(owner,cowner,m);
        // assert klonIdentity(owner,cowner,m);
        // assert (owner != m.o) && (not(outside(owner,m.o)));
        // assert strictlyInside(cowner,m.c);
        // assert (owner != m.o) && (owner != cowner);
        // assert (cowner.owner == mapThruKlon(owner.owner, m));
        // assert (cowner.bound == mapThruKlon(owner.bound, m));

        INSIDE_PARALLEL(o,owner,c,cowner,m);

        assert inside(c, cowner);
        assert ownerStrictlyInside(c,m.c,cowner);
        assert m.m[o] == c; assert m.m[owner] == cowner;
        assert ownerStrictlyInside(m.m[o],m.c,m.m[owner]);
     }

    // assert forall o <- ox, owner <- o.AMFO ::
    //     ownerStrictlyInside(o,m.o,owner) ==> ownerStrictlyInside(m.m[o],m.m[m.o],m.m[owner]);
    // assert forall o <- ox, owner <- o.AMFO ::
    //     ownerStrictlyInside(o,m.o,owner) ==> ownerStrictlyInside(m.m[o],m.c,m.m[owner]);


//    assert mapThruKlon(flownerStrictlyInside(ox,m.o),m) == flownerStrictlyInside(cx,m.c);
  }



lemma INSIDE_PARALLEL(o0 : Object, o1 : Object, c0 : Object, c1 : Object, m : Klon)
 // o0 & o1 are inside the pivot; cloned to c0 and c1
 // o0 is inside o1; ensures c0 inside c1...
 // "CLONING_PRESERVES_INSIDE"??
 decreases o0.AMFO
  requires o0.Ready()
  requires o1.Ready()
  requires c0.Ready()
  requires c1.Ready()
  requires o0 in m.m.Keys
  requires o1 in m.m.Keys
  requires klonCalid(m)
  requires c0 == m.m[o0]
  requires c1 == m.m[o1]

  requires strictlyInside(o0,m.o)
  requires strictlyInside(o1,m.o)
  requires inside(o0,o1)

   ensures strictlyInside(c0,m.c)
   ensures strictlyInside(c1,m.c)
   ensures inside(c0,c1)

  {
    if (o0 == o1) { assert o0 == o1;           assert inside(o0,o1);
                    assert m.m[o0] == m.m[o1]; assert inside(c0,c1);
                    return;  }

    assert o0 != o1;     assert c0 != c1;

    //shoudl this also be WOOD_FOOD?  - is the c0.owner conclusion the important one?
    assert klonLine(o0,c0,m);
    assert klonIdentity(o0,c0,m);
    assert (o0 != m.o) && (not(outside(o0,m.o)));
    assert strictlyInside(c0,m.c);
    assert (o0 != m.o) && (o0 != c0);
    assert c0.owner == mapThruKlon(o0.owner,m);

    if (o1 in o0.owner)
      {
        assert c1 in c0.owner;
        assert inside(c0,c1);
        return;
      }

    assert inside(o0,o1);
    ThereIsALightThatNeverGoesOut(o0,o1);
    var oo := YouCan'tGetThereFromHereBut(o0,o1);
    INSIDE_PARALLEL(oo,o1,m.m[oo],c1,m);
  }











lemma CLONING_PRESERVES_OWNERSHIP(oo : Owner, ob : Bound, co : Owner, cb : Bound, m : Klon)
 //is this name OVERKILL???
 //should it also do bounds?  --- currentlyt NO!
  requires AllReady(oo)
  requires AllReady(ob)
  requires AllReady(co)
  requires AllReady(cb)
  requires klonCalid(m)
  requires m.m.Keys >= oo
  requires m.m.Keys >= ob

 requires boundsOK(oo,ob)
  requires flownerAll(oo) >= flownerAll(ob) // i.e. flatten(oo) >= flatten(ob)
//requires forall o <- oo :: flatten(o.ownerBound()) >= flatten(ob)


  requires co == mapThruKlon(oo, m)
  requires cb == mapThruKlon(ob, m)

// ensures boundsOK(co,cb)
//    ensures flownerAll(co) >= flownerAll(cb)
{
    assert m.o.Ready();      assert m.c.Ready();

     var oo_sp := flownerSplit(oo, m.o);
     var (oo_All, oo_Sin, oo_Out, oo_Pvt, oo_Xpt) := oo_sp;
     assert flownerSplitOK(oo,m.o,oo_sp);

     var ob_sp := flownerSplit(ob, m.o);
     var (ob_All, ob_Sin, ob_Out, ob_Pvt, ob_Xpt) := ob_sp;
     assert flownerSplitOK(ob,m.o,ob_sp);

     var co_sp := flownerSplit(co, m.c);
     var (co_All, co_Sin, co_Out, co_Pvt, co_Xpt) := co_sp;
     assert flownerSplitOK(co,m.c,co_sp);

     var cb_sp := flownerSplit(cb, m.c);
     var (cb_All, cb_Sin, cb_Out, cb_Pvt, cb_Xpt) := cb_sp;
     assert flownerSplitOK(cb,m.c,cb_sp);

     assert flownerSplitOK(oo,m.o,oo_sp);
     assert flownerSplitOK(ob,m.o,ob_sp);
     assert (oo_Sin) !! (oo_Out + oo_Pvt + oo_Xpt);
     assert (ob_Sin) !! (ob_Out + ob_Pvt + ob_Xpt);

     assert oo_All >= ob_All;
     assert oo_Sin >= ob_Sin;
     flownerPivotlyOutside_MONOTONIC(oo,ob,m.o);
     assert flownerPivotlyOutside(oo,m.o) >= flownerPivotlyOutside(ob,m.o);
     assert flownerEverythingOutside(oo,m.o) >= flownerEverythingOutside(ob,m.o);
     assert (oo_Out + oo_Pvt + oo_Xpt) >= (ob_Out + ob_Pvt + ob_Xpt);

     FLOWER_SPLIT_H(oo,ob,m.o);

     DOUBLE_SPLIT_OnlyPivot(oo, co, oo_sp, co_sp, m);
     DOUBLE_SPLIT_OnlyPivot(ob, cb, ob_sp, cb_sp, m);

     assert (m.o in oo_Pvt) <==> (m.c in co_Pvt);
     assert (m.o in ob_Pvt) <==> (m.c in cb_Pvt);
     assert (m.o in oo_Pvt) <==  (m.c in cb_Pvt);
     assert co_Pvt >= cb_Pvt;

     assert co_sp == splitThruKlon(oo,oo_sp,m);
     assert cb_sp == splitThruKlon(ob,ob_sp,m);

     assert oo_All >= ob_All;

     assert oo_Sin >= ob_Sin;
     assert oo_Out >= ob_Out; //Err
     assert oo_Pvt >= ob_Pvt;
     assert oo_Xpt >= ob_Xpt; //Err

     assert co_Sin >= cb_Sin; //Err
     assert co_Out >= cb_Out; //Err
     assert co_Pvt >= cb_Pvt;
     assert co_Xpt >= cb_Xpt; //Err

     assert co_All >= cb_All;
}

//
// lemma NUKE_MAPPED_GEQ(oo : Owner, ob : Bound, co : Owner, cb : Bound, m : Klon)
//   requires AllReady(oo)
//   requires AllReady(ob)
//   requires AllReady(co)
//   requires AllReady(cb)
//   requires klonCalid(m)
//   requires m.m.Keys >= oo
//   requires m.m.Keys >= ob
//
// //requires boundsOK(oo,ob)
//   requires flatten(oo) >= flatten(ob)
// //requires forall o <- oo :: flatten(o.ownerBound()) >= flatten(ob)
//
//   requires co == mapThruKlon(oo, m)
//   requires cb == mapThruKlon(ob, m)
//
// // ensures boundsOK(co,cb)
// // ensures flatten(co) >= flatten(cb)
// // ensures forall o <- co :: flatten(o.ownerBound()) >= flatten(cb)
// {
//   var pivot  := m.o;
//   var blivet := m.c;
//
//   assert flatten(oo) >= flatten(ob);
// //  assert forall o <- oo :: flatten(o.ownerBound()) >= flatten(ob);
//
//   var noo := nuke(oo);
//   var nob := nuke(ob);
//   var nco := nuke(co);
//   var ncb := nuke(cb);
//
//   FLATTEN_NUKE(oo);
//   assert noo == nuke(oo) == flatten(oo);
//   FLATTEN_NUKE(ob);
//   assert nob == nuke(ob) == flatten(ob);
//
//
//   var out_oo := nukeOutside(oo,pivot);
//   var sin_oo := nukeStrictlyInside(oo,pivot);
//   var pvt_oo := nukeStrictlyPivot(oo,pivot);
//   nukeEmAll3(oo,pivot,out_oo,sin_oo,pvt_oo,noo);
//   assert out_oo + sin_oo + pvt_oo == noo;
//
// //assert (out_oo + pvt_oo) !! sin_oo;
//
//
//   var out_ob := nukeOutside(ob,pivot);
//   var sin_ob := nukeStrictlyInside(ob,pivot);
//   var pvt_ob := nukeStrictlyPivot(ob,pivot);
//   nukeEmAll3(ob,pivot,out_ob,sin_ob,pvt_ob,nob);
//   assert out_ob + sin_ob + pvt_ob == nob;
//
//
//
//
//
//   FLATTEN_NUKE(co);
//   assert nco == nuke(co) == flatten(co);
//   FLATTEN_NUKE(cb);
//   assert ncb == nuke(cb) == flatten(cb);
//
//   // assert flatten(co) >= flatten(cb);
//   // assert forall o <- co :: flatten(o.ownerBound()) >= flatten(cb);
//
// }
