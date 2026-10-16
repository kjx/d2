include "Ownership.dfy"
include "Ownership-Pivot.dfy"
include "Klon-Split.dfy"

//originally named Ownership-Dunno cos I didn't know whwat else to call it
//perhaps functions wiht the PIVOT stay here ("Onwership-Pivot")
//functions with the KLON goto Klon-Ownership or **Klon-Pivot**
//the NUKE methods I think are all DEAD - now removed
//the ones w'ere running with now are flowner -> flatten owner  flowner(owners,pivot) -> flattened owners :-)










///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////
//// "Flatten" functions - functions that flatten a "soup" into a set  divided in some why with a pivo
////    more or less repalced by "Flowner" versions which I thought were better cos they could
////   cope with the tricky e.g. outsidePivot cases/
////   (but now I'm not sure they can - 16Oct 2026.)
////




///Oh SHIT 0 most of the these are WRONG. - notably the ones iwth the PIVOT,
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

function flattenOnlyPivot(soup : OWNR, pivot : Object)  : (rv : Owner)
 {set s <- soup, oo <- s.AMFO | onlyPivot(s,pivot,oo) :: oo}
// snuck iinto Ownerehsip-Pivot.dfy...

function flattenExceptPivot(soup : OWNR, pivot : Object) : (rv : Owner)
 {set s <- soup, oo <- s.AMFO | exceptPivot(s,pivot,oo) :: oo}

function flattenOutsidePivot(soup : OWNR, pivot : Object) : (rv : Owner)
 {set s <- soup, oo <- s.AMFO | outsidePivot(s,pivot,oo) :: oo}

lemma LEMMA_flattenOutsudePivot0(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == flattenOutsidePivot(soup, pivot))

   ensures forall r <- rv :: inside(pivot, r)
   ensures forall r <- rv :: exists s <- soup :: onlyPivot(s,pivot,r)
{}


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



////////////////////////////////////////////////////
////////////// FLOWNER FLATTENs

lemma FLOWNER_FLATTEN_Outside(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()
   ensures flattenOutside(soup, pivot) == flownerOutside(soup, pivot)
{}


lemma FLOWNER_FLATTEN_TODO_FOR_ALL(soup : OWNR, pivot : Object)
 //verified 21 Sep 2026
  requires AllReady(flatten(soup)) && pivot.Ready()

   ensures flattenOutside(soup, pivot) == flownerOutside(soup, pivot)
   ensures flattenOnlyPivot(soup, pivot) == flownerOnlyPivot(soup, pivot)
   ensures flattenPivotlyOutside(soup, pivot) == flownerPivotlyOutside(soup, pivot)
   ensures flatten(soup) == flownerAll(soup)
{}




lemma {:timeLimit 70} FLOWNER_FLATTEN_Outside_Klon(soup : OWNR, m : Klon)
 //DOESN WOKR LIsKELY FOR THE USUAL OOD REASON OH FUCK
 //that's another day I'll never get back
  requires AllReady(flatten(soup))
  requires klonCalid(m)
  requires soup <= m.m.Keys
   ensures flatten(soup) <= m.m.Keys
  // ensures flownerOutside(mtk(soup,m), m.c) == mtk(flownerOutside(soup,m.o), m)
{
  assume forall x : Object :: x.Ready();
  assume forall x : set<Object> :: AllReady(x);


//  var ffOm :=  flownerOutside(mtk(soup,m), m.c);
  var coup := mtk(soup,m);
  assert forall c <- coup | outside(c,m.c)  :: c in soup;
  assert forall s <- soup | outside(s,m.o)  :: s in coup;
  assert   (set c <- coup | outside(c,m.c)) == (set s <- soup | outside(s,m.o));

  var fsoup := flatten(soup);
  var fcoup := mtk(fsoup,m);

  assert forall c <- fcoup | outside(c,m.c)  :: c in fsoup;
  assert forall s <- fsoup | outside(s,m.o)  :: s in fcoup;
  assert   (set c <- fcoup | outside(c,m.c)) == (set s <- fsoup | outside(s,m.o));

  assert flattenOutside(mtk(soup,m), m.c) == flownerOutside(mtk(soup,m), m.c)
    by { FLOWNER_FLATTEN_Outside(mtk(soup,m),m.c); }

  assert forall o <- m.m.Keys | outside(o, m.o) :: m.m[o] == o;

  assert flattenOutside((set s <- soup :: m.m[s]), m.c)                          == flattenOutside(mtk(soup,m), m.c);
  assert flattenOutside((set s <- soup :: m.m[s]), m.c)                          == flattenOutside(mtk(soup,m), m.c);
  assert (set x <- flatten(  (set s <- soup :: m.m[s])  ) | outside(x,m.c))      == flattenOutside((set s <- soup :: m.m[s]), m.c) by
                                                                                       { var r := flattenOutside((set s <- soup :: m.m[s]), m.c);
                                                                                         FLOWNER_FLATTEN_Outside_Klon_03(soup,m,r); }


   assert (set x <- flatten(  (set s <- soup :: m.m[s])  ) | outside(x,m.c) :: x) == (set x <- flatten(  (set s <- soup :: m.m[s])  ) | outside(x,m.c)) by
                                                                                       { var r :=  (set x <- flatten(  (set s <- soup :: m.m[s])  ) | outside(x,m.c));
                                                                                         FLOWNER_FLATTEN_Outside_Klon_04(soup,m,r); }


  // assert (set x <- flatten(  (set s <- soup ::     s)   ) | outside(m.m[x],m.c) :: m.m[x]) == (set x <- flatten(  (set s <- soup :: m.m[s])  ) | outside(x,m.c) :: x);

 // assert flattenOutside(mtk(soup,m), m.c) == flownerOutside(mtk(soup,m), m.c);
}

lemma {:timeLimit 7} FLOWNER_FLATTEN_Outside_Klon_03(soup : OWNR, m : Klon, r : Owner)
  requires AllReady(flatten(soup)) && AllReady(flatten(r)) && klonCalid(m)
  requires soup <= m.m.Keys
   ensures flatten(soup) <= m.m.Keys
  requires r == flattenOutside((set s <- soup :: m.m[s]), m.c)
   ensures r == (set x <- flatten(  (set s <- soup :: m.m[s])  ) | outside(x,m.c))
   {}


lemma {:timeLimit 7} FLOWNER_FLATTEN_Outside_Klon_04(soup : OWNR, m : Klon, r : Owner)
  requires AllReady(flatten(soup)) && AllReady(flatten(r)) && klonCalid(m)
  requires soup <= m.m.Keys
   ensures flatten(soup) <= m.m.Keys
  requires r == (set x <- flatten(  (set s <- soup :: m.m[s])  ) | outside(x,m.c))
   ensures r == (set x <- flatten(  (set s <- soup :: m.m[s])  ) | outside(x,m.c) :: x)
   {}



























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


lemma NUKE_DICHOTOMY_TRICHOTOMY(soup : Owner, pivot : Object, left0 : Owner, left1 : Owner, right : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
 requires left0 == flattenExceptPivot(soup,pivot)
 requires left1 == flattenOnlyPivot(soup,pivot)
 requires right == flattenOutsidePivot(soup,pivot)

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

   ensures (outsidePivot(o, pivot, owner)) <==>
                     (onlyPivot(o,pivot,owner) || exceptPivot(o,pivot,owner))

   ensures (inside(o, pivot)) <==>
                     (onlyPivot(o,pivot,owner) || exceptPivot(o,pivot,owner))

   ensures outsidePivot(o,pivot,owner) == (onlyPivot(o,pivot,owner) || exceptPivot(o,pivot,owner))

   ensures ownerOutsidePivot(o,pivot,owner) ==
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



   ensures  inside(o,pivot)  != outside(o,pivot)
   ensures  inside(owner,pivot) != outside(owner,pivot)
{}






lemma KRX(k : Object, m : Klon)
  requires klonCalid(m)
   ensures outside(m.o,m.c)
   ensures forall x <- m.m.Keys | outside(x,m.o) :: outside(x,m.c)
{}













/////////////////////////////////////////////////////////////////
//// "twice" functions    --- DOUBLE lemmas



function flattenTwiceStictlyOutside(soup : OWNR, pivot : Object) : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
  {
    (set s <- flatten(soup), t <- flatten(soup) | inside(s,t) && outside(t,pivot) &&  outside(s,pivot) :: t)
  }

//flownerExistentialStictlyOutsiode
function flownerTwiceStictlyOutside(soup : OWNR, pivot : Object) : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
  {
    (set s <- flownerAll(soup), t <- flownerAll(soup) | inside(s,t) && outside(t,pivot) && outside(s,pivot) :: t)
  }

function flownerExistentialStictlyOutside(soup : OWNR, pivot : Object) : (rv : Owner)
    requires AllReady(flatten(soup)) && pivot.Ready()
  {
    (set t <- flownerAll(soup) | (exists s <- flownerAll(soup) :: inside(s,t) && outside(t,pivot) &&  outside(s,pivot)) :: t)
  }







lemma DOUBLE_SPLIT(os : Owner, cs : Owner, os_sp : FlownerSplit, cs_sp : FlownerSplit, m : Klon)
  requires AllReady(flatten(os)) && AllReady(flatten(cs))
  requires klonCalid(m)
  requires m.m.Keys >= os
  requires cs == mapThruKlon(os,m)
  requires flownerSplitOK(os, m.o, os_sp)
  requires flownerSplitOK(cs, m.c, cs_sp)
   ensures os_sp.fAll == flownerAll(os)
   ensures cs_sp.fAll == flownerAll(cs)
 {
   assert os_sp.fSin == flownerStrictlyInside(os,m.o);
   assert cs_sp.fSin == flownerStrictlyInside(cs,m.c);
   //FOREST_FOOD(os_sp.fSin, cs_sp.fSin, m);
 }









lemma DOUBLE_SPLIT_Outside(os : Owner, cs : Owner, os_sp : FlownerSplit, cs_sp : FlownerSplit, m : Klon)
 //verified 21Sep2026  (well; kinda)  --- except the last two crucial ensures below
  requires AllReady(flatten(os)) && AllReady(flatten(cs))
  requires klonCalid(m)
  requires m.m.Keys >= os
  requires cs == mapThruKlon(os,m)
  requires flownerSplitOK(os, m.o, os_sp)
  requires flownerSplitOK(cs, m.c, cs_sp)
   ensures os_sp.fAll == flownerAll(os)
   ensures cs_sp.fAll == flownerAll(cs)
   ensures os_sp.fOut == flownerStrictlyOutside(os, m.o)
   ensures cs_sp.fOut == flownerStrictlyOutside(cs, m.c)
   ensures os_sp.fXpt == flownerExceptPivot(os, m.o)
   ensures cs_sp.fXpt == flownerExceptPivot(cs, m.c)

   ensures os_sp.fOut == cs_sp.fOut   //ERR
   ensures os_sp.fXpt == cs_sp.fXpt   //ERR
{
   assert m.m.Keys >= os_sp.fOut;
   assert m.m.Keys >= os_sp.fXpt;

   flownerStrictlyOutside_OUTSIDE(os, os_sp.fOut, m.o);
   flownerStrictlyOutside_OUTSIDE(cs, cs_sp.fOut, m.c);
   flownerExceptPivot_OUTSIDE(os, os_sp.fXpt, m.o);
   flownerExceptPivot_OUTSIDE(cs, cs_sp.fXpt, m.c);

}






lemma flownerStrictlyOutside_OUTSIDE(os : Owner, FFO : Owner, pivot : Object)
//verified 22 sept
  requires AllReady(flatten(os))
  requires AllReady(flatten(FFO))
  requires pivot.Ready()
  requires FFO == flownerStrictlyOutside(os, pivot)
   ensures forall f <- FFO :: outside(f,pivot)
{}

lemma flownerExceptPivot_OUTSIDE(os : Owner, FEP : Owner, pivot : Object)
   //verified 22 sept
  requires AllReady(flatten(os))
  requires AllReady(flatten(FEP))
  requires pivot.Ready()
  requires FEP == flownerExceptPivot(os, pivot)
   ensures forall f <- FEP :: outside(f,pivot)
{}







lemma XLR(x : Owner, l : Owner, r : Owner, m : Klon)
//dpes peove22

//consider a larger hammer??
///see MAP_THRU_KLON currently in Klon.dfy
////see also FLOWNER_STRICTLY_OUTSIDE_THRU_KLON etc
  requires AllReady(flatten(x))
  requires AllReady(flatten(l))
  requires AllReady(flatten(r))
  requires klonCalid(m)
  requires x <= m.m.Keys
  requires l == flownerStrictlyOutside(x, m.o)
  requires r == flownerStrictlyOutside(mapThruKlon(x, m), m.c)

  // ensures outside(m.o,m.c)
  ensures l == r  //Err
  {
   flownerStrictlyOutside_OUTSIDE(x, l, m.o);
   flownerStrictlyOutside_OUTSIDE(mapThruKlon(x, m), r, m.c);

assert l == (set o <- x, owner <- o.AMFO | PART_INSIDE_OWNER(x,m.o); ownerStrictlyOutside(o,m.o,owner) :: owner);

assert r == (set o <- mapThruKlon(x,m), owner <- o.AMFO | PART_INSIDE_OWNER(x,m.c); ownerStrictlyOutside(o,m.c,owner) :: owner);

// assert forall o <- x, owner <- o.AMFO | PART_INSIDE_OWNER(x,m.o); ownerStrictlyOutside(o,m.o,owner) :: outside(owner,m.o);

assert forall owner <- l :: outside(owner,m.o);
assert forall owner <- r :: outside(owner,m.o);

 var xx := mapThruKlon(x,m);
MAP_THRU_KLON(x,xx,m);

assert l == r;

  //  assert flownerStrictlyOutside(x, m.o) ==
  //     (set o <- x, owner <- o.AMFO
  //       | PART_INSIDE_OWNER(x,m.o); ownerStrictlyOutside(o,m.o,owner) :: owner);
  }











lemma FUCK_YOU_TORY_CUNT(soup : OWNR, pivot : Object)
   requires AllReady(flatten(soup)) && pivot.Ready()
    ensures shortcutOnlyPivot(soup, pivot) == flattenOnlyPivot(soup, pivot)

 {
   LEMMA_shortcutVSflatten2(soup, pivot, shortcutOnlyPivot(soup, pivot), flattenOnlyPivot(soup, pivot));
}
