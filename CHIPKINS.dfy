
include "Ownership-Recursive.dfy"
include "Set-Lemmata.dfy"
include "Ownership-Recursive.dfy"
include "Ownership-Parallel.dfy"
include "Ownership-Trilemma.dfy"
include "Context.dfy"





predicate ONE_FOURTH(os : Owner, pivot : Object,  sp : Owner, above : Owner, middle : Owner, below : Owner)
  {
//readiness - not covered in this version
//     && (AllReady(oo))
//     && (klonReady(m))
//     && (klonCalid(m))

//geometery & progress - not covered in this version
//     && (m.m.Keys >= flatten(oo) >= oo >= {next})
//     && (oo     == todo + {next} + done)
//     && (todo !! {next} !! done)
//     && (next in m.m.Keys)
//     && (cext == m.m[next])
//     && (next.Ready())
//     && (cext.Ready())
//     && (klonLine(next,cext,m))

    && (sp    == flatten(os))
//LOOP   && (sp    == above + middle + below)

    && (below == (set x <- sp | strictlyInside(x,pivot)))
    // && (below == collectAllInside(xxx,pivot))
    && (middle == (if (pivot in sp) then (pivot.AMFO) else {}))
    && (above  == fOutside(os, pivot))

        // && (cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c))
    // && (oabove' == cabove')
  }


    // && (osp    == osp' + next.AMFO)
    // && (csp    == csp' + cext.AMFO)
    // && (osp    == flatten(done+{next}))
    // && (csp    == flatten(mapThruKlon(done+{next}, m)))
    //U3
    //  ensures obelow  == (set x <- osp | strictlyInside(x,m.o))
    //  ensures cbelow  == (set x <- csp | strictlyInside(x,m.c))
    //U4
    //  ensures oabove == fOutside((done+{next})-{m.o}, m.o)
    //  ensures cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c)



// predicate DELTA_FOURTH(done : Owner, m : Klon, delta : Object) { ONE_FOURTH(done+delta, m) } }


lemma {:timeLimit 100} CAXE_UALL_INSIDE(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
         returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)


//////////////////////////////////////////////////////////////////////
//
    requires strictlyInside(next, m.o)

    requires AllReady(oo)
    requires klonReady(m)               requires KRDY: klonReady(m)
    requires klonCalid(m)               requires KCLD: klonCalid(m)
    requires m.m.Keys >= flatten(oo) >= oo
    requires oo == todo + {next} + done
    requires todo !! {next} !! done

    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)

     ensures next.Ready()
     ensures cext.Ready()


//LOOP    requires osp'    == obelow' + oabove' + opivot'
    requires osp'    == flatten(done)
 //LOOP   requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))

    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})
    requires oabove' == fOutside(done, m.o)
    requires cabove' == fOutside(mapThruKlon(done,m), m.c)
//LOOP    requires oabove' == cabove'

//////////////////////////////////////////////////////////////////////

// //
//      ensures AllReady(oo)
//      ensures klonReady(m)
//      ensures klonCalid(m)
// //
//      ensures oo    == todo + {next} + done
//      ensures todo  !! {next} !! done
//      ensures osp   == obelow + oabove + opivot
//      ensures osp   == flatten(done+{next})
//      ensures csp   == cbelow + cabove + cpivot
//      ensures csp   == flatten(mapThruKlon(done+{next}, m))
// //
//      ensures oabove == oabove'
//      ensures cabove == cabove'
//      ensures opivot == opivot'
//      ensures cpivot == cpivot'
//      ensures obelow == obelow' + collectAllInside(next,m.o)
//      ensures cbelow == cbelow' + collectAllInside(cext,m.c)
//
//      ensures oabove == fOutside(done+{next}-{m.o}, m.o)
//      ensures cabove == fOutside(mapThruKlon(done+{next}-{m.o},m),m.c)
//     //  ensures oabove == fOutside(done-{m.o}, m.o)
//     //  ensures cabove == fOutside(mapThruKlon(done-{m.o},m), m.c)
//      ensures oabove == cabove
//      ensures opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {})
//      ensures cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {})
//      ensures obelow == (set x <- osp | strictlyInside(x,m.o))
//      ensures cbelow == (set x <- csp | strictlyInside(x,m.c))

    // see sp=below+above+pivot  (or above+pivot+below - canonical order??)
    //  ensures OOOO(osp,obelow,oabove,opivot)
    //  ensures OOOO(csp,cbelow,cabove,cpivot)

    //see IN_N_OUT_BURGER(oo, m)
    //  ensures forall x <- done+{next} |  inside(x,m.o) ::  inside(m.m[x],m.c)
    //  ensures forall x <- done+{next} | outside(x,m.o) :: (m.m[x] == x) // && (m.m[x] in csp)
    //  ensures forall x <- flatten(done+{next}) |  inside(x,m.o) ::  inside(m.m[x],m.c)
    //  ensures forall x <- flatten(done+{next}) | outside(x,m.o) :: (m.m[x] == x) // && (m.m[x] in csp)

     ensures IN_N_OUT_BURGER(oo, m)
{

    // assert obelow' == (set x <- osp' | strictlyInside(x,m.o));
    // assert cbelow' == (set x <- csp' | strictlyInside(x,m.c));

    IN_N_OUT_LEMMER(oo, m);
    assert IN_N_OUT_BURGER(oo, m);

//////////////////////////////////////////////////////////////////////
//
var obelow_ := collectAllInside(next,m.o);  // assert OBELOW: obelow_ == collectAllInside(next,m.o);
var cbelow_ := collectAllInside(cext,m.c);  // assert CBELOW: cbelow_ == collectAllInside(cext,m.c);

    obelow := obelow' + obelow_;
    cbelow := cbelow' + cbelow_;

// opaque {
//    assert obelow_ == collectAllInside(next,m.o) by { reveal OBELOW; }
//    assert cbelow_ == collectAllInside(cext,m.c) by { reveal CBELOW; }
//    assert obelow  == obelow' + obelow_;
//    assert cbelow  == cbelow' + cbelow_;
//    assert obelow  == obelow' + collectAllInside(next,m.o);
//    assert cbelow  == cbelow' + collectAllInside(cext,m.c);
// }
    oabove := oabove';
    cabove := cabove';
    opivot := m.o.AMFO;
    cpivot := m.c.AMFO;
    osp    := obelow + oabove + opivot;
    csp    := cbelow + cabove + cpivot;
//
//     assert (opivot' == {}) != (opivot' == m.o.AMFO);
//     assert (cpivot' == {}) != (cpivot' == m.c.AMFO);
//     AddEmptySetBefore({} + m.o.AMFO, m.o.AMFO);
//     AddEmptySetBefore({} + m.c.AMFO, m.c.AMFO);
//     // assert {} + m.o.AMFO == m.o.AMFO;
//     // assert {} + m.c.AMFO == m.c.AMFO;
//     // assert m.o.AMFO + m.o.AMFO == m.o.AMFO;
//     // assert m.c.AMFO + m.c.AMFO == m.c.AMFO;
//     assert opivot == m.o.AMFO;
//     assert cpivot == m.c.AMFO;

//
//
// assert
// //readiness - not covered in this version
//     && (AllReady(oo))
//     && (klonReady(m))
//     && (klonCalid(m))
// //geometery & progress - not covered in this version
//     && (m.m.Keys >= flatten(oo) >= oo >= {next})
//     && (oo     == todo + {next} + done)
//     && (todo !! {next} !! done)
//     && (next in m.m.Keys)
//     && (cext == m.m[next])
//     && (next.Ready())
//     && (cext.Ready())
//     && (klonLine(next,cext,m))
//     ;

//predicate ONE_FOURTH(os : Owner, pivot : Object,  sp : Owner, above : Owner, middle : Owner, below : Owner)

 assert obelow' == (set x <- osp' | strictlyInside(x,m.o));
 assert cbelow' == (set x <- csp' | strictlyInside(x,m.c));

assert ONE_FOURTH(done,                       m.o, osp', oabove', opivot', obelow');
// assert ONE_FOURTH(done+{next},                m.o, osp,  oabove,  opivot,  obelow);
// assert ONE_FOURTH(mapThruKlon(done,m),        m.c, csp', cabove', cpivot', cbelow');
// assert ONE_FOURTH(mapThruKlon(done+{next},m), m.c, csp,  cabove,  cpivot,  cbelow);

// Could not prove: sp == above + middle + below
// Could not prove: below == (set x <- sp | strictlyInside(x,pivot))
// Could not prove: above == fOutside(os, pivot)

//////////////////////////////////////////////////////////////////////
//
//     GEFUCKENMILLER(osp, obelow', oabove', opivot', obelow_);
//     GEFUCKENMILLER(csp, cbelow', cabove', cpivot', cbelow_);
//
//////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////
//
// assert obelow' == (set x <- osp' | strictlyInside(x,m.o)) by { reveal OBSI; }
// assert cbelow' == (set x <- csp' | strictlyInside(x,m.c)) by { reveal CBSI; }
//
// assert obelow == obelow' + collectAllInside(next,m.o);
// assert cbelow == cbelow' + collectAllInside(cext,m.c);
//
//     assert (strictlyInside(next,m.o));
//     assert (AllReady(oo));
//     assert (klonReady(m))  by { reveal KRDY; }
//     assert (klonCalid(m))  by { reveal KCLD; }
//     assert (m.m.Keys >= flatten(oo) >= oo);
//     assert (next in m.m.Keys);
//     assert (cext == m.m[next]);
//     assert (klonLine(next,cext,m));
//
//     assert (oo     == todo + {next} + done);
//     assert (todo !! {next} !! done);
//
//     assert (osp'    == obelow' + oabove' + opivot');
//     assert (osp' == flatten(done));
//     assert (csp'    == cbelow' + cabove' + cpivot');
//     assert (csp'    == flatten(mapThruKlon(done, m)));
//
//     assert (obelow' == (set x <- osp' | strictlyInside(x,m.o)));
//     assert (cbelow' == (set x <- csp' | strictlyInside(x,m.c)));
//     assert (oabove' == fOutside(done-{m.o}, m.o));
//     assert (cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c));
//     assert (oabove' == cabove');
//     assert (opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {}));
//     assert (cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {}));
//
//     assert (obelow == obelow' + collectAllInside(next,m.o)) by { reveal OBELOW, OBSI; }
//     assert (cbelow == cbelow' + collectAllInside(cext,m.c)) by { reveal CBELOW, CBSI; }
//     assert (oabove == oabove');
//     assert (cabove == cabove');
//     assert (opivot == opivot');
//     assert (cpivot == cpivot');
//
//     // assert (osp    == flatten(done));
//     // assert (csp    == flatten(mapThruKlon(done, m)));
//     assert (osp    == obelow + oabove + opivot);
//     assert (csp    == cbelow + cabove + cpivot);
//
//////////////////////////////////////////////////////////////////////


    // assert REQ_INSIDE(oo, m, done, todo, next, cext,
    //                   osp', obelow', oabove', opivot',
    //                   csp', cbelow', cabove', cpivot',
    //                   osp, obelow, oabove, opivot,
    //                   csp, cbelow, cabove, cpivot)
    //                   by { reveal REQ_INSIDE(); }

//
//     CASE_INSIDE_U0(oo, m, done, todo, next, cext,  //ERR
//                   osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
//                   osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
//     CASE_INSIDE_U1(oo, m, done, todo, next, cext,
//                   osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
//                   osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
//     CASE_INSIDE_U2(oo, m, done, todo, next, cext,
//                   osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
//                   osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
//     CASE_INSIDE_U3(oo, m, done, todo, next, cext,  //ERR
//                   osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
//                   osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
//     CASE_INSIDE_U4(oo, m, done, todo, next, cext,
//                   osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
//                   osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
//     CASE_INSIDE_U5(oo, m, done, todo, next, cext,
//                   osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
//                   osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
//     CASE_INSIDE_U6(oo, m, done, todo, next, cext,
//                   osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
//                   osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
}






lemma Trilemma_INSIDE(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                 o' : Trilemma, c' : Trilemma)
         returns (o : Trilemma, c  : Trilemma)

    requires strictlyInside(next, m.o)

    requires AllReady(oo)
    requires klonReady(m)               requires KRDY: klonReady(m)
    requires klonCalid(m)               requires KCLD: klonCalid(m)
    requires m.m.Keys >= flatten(oo) >= oo
    requires oo == todo + {next} + done
    requires todo !! {next} !! done

    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)

    requires o'.owners == oo
    requires o'.pivot == m.o
    requires c'.owners == mapThruKlon(oo,m)
    requires c'.pivot == m.c

    //  ensures next.Ready()
    //  ensures cext.Ready()

{
//   assert o'.Valid();
//
//   assert (next.Ready() && cext.Ready()) by { assert klonLine(next,cext,m); }
//   o'.LEMMA_below();
//   assert o'.PRED_below1();
//   assert o'.PRED_below2();
//   //assert (o'.below == (set x <- o'.flatness | strictlyInside(x,o'.pivot))) by { assert o'.PRED_below1(); }
//   assert o'.below == flattenStrictlyInside(o'.owners, o'.pivot);
//   assert o'.below == allStrictlyInside(o'.flatness,o'.pivot);
//
//   assert
//     && (o'.flatness == flatten(o'.owners))
//     && (o'.below == flattenStrictlyInside(o'.owners, o'.pivot))
//     && (o'.middle == (if (o'.pivot in o'.flatness) then (o'.pivot.AMFO) else {}))
//     && (o'.above  == flattenOutside(o'.owners, o'.pivot))
//     && (o'.flatness == o'.above + o'.middle + o'.below)
//     ;

    FLATTEN_DELTA(o'.owners, next);
    assert flatten(o'.owners + {next}) == (flatten(o'.owners) + next.AMFO);

    flattenStrictlyInside_DELTA(o'.owners, next, m.o);
    assert flattenStrictlyInside(o'.owners+{next}, m.o) == (flattenStrictlyInside(o'.owners,m.o) + flattenStrictlyInside({next},m.o));

    var z : Trilennnna :=
         o'.(  owners := o'.owners + {next},
             flatness := o'.flatness + next.AMFO,
                below := o'.below + flattenStrictlyInside({next},m.o),
               middle := (if (o'.pivot in o'.flatness) then (o'.pivot.AMFO) else (o'.middle)),
                above := flattenOutside(o'.owners + {next}, o'.pivot) //this is either EVIL or evil...
             );

    assert
       && (z.flatness == flatten(z.owners))
       && (z.below == flattenStrictlyInside(z.owners, z.pivot))
       && (z.middle == (if (z.pivot in z.flatness) then (z.pivot.AMFO) else {}))
       && (z.above  == flattenOutside(z.owners, z.pivot))
       && (z.flatness == z.above + z.middle + z.below)
    ;

    o := z;
    c := c';
    // c := c'.(owners := o'.owners + {next},
    //          flatness := c'.flatness + cext.AMFO,
    //          below := c'.below + allStrictlyInside(cext.AMFO,m.c));
}



lemma FLATTEN_DELTA(o' : Owner, o_ : Object)
 requires o_.Ready()
  ensures flatten(o'+{o_}) == flatten(o') + o_.AMFO
  ensures flatten(o'+{o_}) == flatten(o') + argh(o_)
  {
    FLATTEN1(o', o_,  o'+{o_});
  }


lemma StrictlyInside_DELTA(o' : Owner, o_ : Object, pivot : Object)
 requires o_.Ready()
  ensures allStrictlyInside(flatten(o'+{o_}), pivot) == allStrictlyInside(flatten(o'), pivot) + allStrictlyInside(o_.AMFO,pivot)
  {       }

lemma flattenStrictlyInside_DELTA(o' : Owner, o_ : Object, pivot : Object)
 requires o_.Ready()
  ensures flattenStrictlyInside((o'+{o_}),pivot) == flattenStrictlyInside(o',pivot) + flattenStrictlyInside({o_},pivot)
  {  }









































































predicate {:timeLimit 15} IN_N_OUT_BURGER(oo : Owner, m : Klon)
  //that original & clones in m.m are either both inside the pivot
  //or outside the pivot and identical :-)
   requires oo <= m.m.Keys
   requires AllReady(oo)
   requires klonReady(m)
   requires klonCalid(m)
      reads m.hns()
  {
    && (forall x <- oo |  inside(x,m.o) ::  inside(m.m[x],m.c))
    && (forall x <- oo | outside(x,m.o) :: (m.m[x] == x) )
    && (forall x <- flatten(oo) |  inside(x,m.o) ::  inside(m.m[x],m.c))
    && (forall x <- flatten(oo) | outside(x,m.o) ::  (m.m[x] == x))
  }

lemma IN_N_OUT_DELTA(o : Owner, o' : Owner, o_  : Owner, m : Klon)
    requires o  == o' + o_
    requires o <= m.m.Keys
    requires AllReady(o)
    requires klonReady(m)
    requires klonCalid(m)
    requires IN_N_OUT_BURGER(o', m)
    requires IN_N_OUT_BURGER(o_, m)
     ensures IN_N_OUT_BURGER(o,  m)
{ FLATTEN_SUMS(o',o_,o,m); }




lemma FLATTEN_SUMS(a : Owner, b : Owner, c : Owner, m : Klon)
  //just say  FLATTEN_SUMS(done,{next},done+{next},m);

  requires a+b == c
  // requires forall o <- a :: o.Ready()  //I'm OH SO TORY
  // requires forall o <- b :: o.Ready()  //I'm OH SO TORY
  // requires forall o <- c :: o.Ready()  //TORY TORY TORY
  //  requires AllReady(a)
  //  requires AllReady(b)
  //  requires AllReady(c)
  //  requires klonReady(m)
  //  requires klonCalid(m)
  requires (a+b+c) <= m.m.Keys
  //    ensures recFlatten(a)+recFlatten(b)==recFlatten(a+b)
  ensures flatten(a) + flatten(b) == flatten(a+b)
  ensures mapThruKlon(a,m) + mapThruKlon(b,m) == mapThruKlon(a+b,m)
  ensures mapThruKlon(a+b,m) == mapThruKlon(a,m) + mapThruKlon(b,m)
  ensures flatten(mapThruKlon(a,m)) + flatten(mapThruKlon(b,m)) == flatten(mapThruKlon(a+b,m))
  ensures flatten(mapThruKlon(a+b,m)) == flatten(mapThruKlon(a,m)) + flatten(mapThruKlon(b,m))
{}



lemma IN_N_OUT_LEMMER(oo : Owner, m : Klon)
   requires oo <= m.m.Keys
   requires klonReady(m)
   requires klonCalid(m)

    ensures IN_N_OUT_BURGER(oo,m)
{
    assert m.m.Keys >= flatten(oo);

    assert forall o <- oo :: o.Ready();
    assert forall o <- oo :: m.m[o].Ready();

    assert forall o <- oo :: klonLine(o,m.m[o],m);
    assert forall o <- oo :: klonGeometry(o,m.m[o],m);
    assert forall o <- oo :: m.objectReadyInKlown(o);
    assert forall o <- flatten(oo) :: klonGeometry(o,m.m[o],m);
}
  // {
  //   assert



function  fOutside(ownrs : OWNR, pivot : Object) : (rv : Owner)
//rename to allLOutside???
//KJX FUCK FUCK FUCK FUCK FUCK FUCK
//returns all flatatnened owners that are outside the pivot...
//YEAH I fear this is still the WRONG THING
//shop;dln't it take in all the *direct* owners
//throw out all that are inside
//and flatten the remainder (outside ONLY)
  // requires AllReady(flatten(ownrs))
  // requires pivot.Ready()
  //  ensures AllReady(rv)
  ensures forall r <- rv :: outside(r,pivot)
{ set x <- flatten(ownrs) | outside(x,pivot) } // not(strictlyInside(x, pivot)) }



//THIS SSHIT IS ALL WRONG
//
// function flattenOnlyPivot(ownrs : OWNR, pivot : Object) : (rv : Owner)
//   ensures forall r <- rv :: onlyPivot(r,pivot)
//   ensures forall r <- flatten(ownrs) :: onlyPivot(r,pivot) ==> r in rv
// { set x <- flatten(ownrs) | onlyPivot(x,pivot) }
//
//
// predicate onlyPivot(r : Object, pivot : Object) {r in pivot.AMFO}
//
// lemma flattenOnlyPivot_GETS_ONLYPIVOT(ownrs : OWNR, pivot : Object, rv : Owner)
//    requires rv == flattenOnlyPivot(ownrs,pivot)
//     ensures (pivot in flatten(ownrs)) ==> (rv == pivot.AMFO)
//     ensures (pivot !in flatten(ownrs)) ==> (rv == {})
//     // ensures (rv == {}) != (rv == pivot.AMFO)
//     {}
//
//



// function collectAllInside(o : Object, pivot : Object) : (rv : set<Object>)
//   // all o's transitive owners strictly inside pivot
//   // recursive, shortcutting analogue of allInside
//   decreases o.AMFO
//    requires o.Ready()  //GRR
//     {
//       if (not(strictlyInside(o,pivot))) then ({})
//           else  {o} + (set oo <- o.owner, ooo <- collectAllInside(oo, pivot) :: ooo)
//     }



function flattenAllInside(os : Owner, pivot : Object) : (rv : set<Object>)
  // all o's transitive owners strictly inside pivot
  // recursive, shortcutting analogue of allInside
   requires AllReady(os)
    requires forall oo <- os :: oo.Ready()
    {set oo <- os, ooo <- collectAllInside(oo,pivot) :: ooo}


lemma INCREMENTAL_AllInside(next : Object, os : Owner, pivot : Object)
  requires next.Ready()
  requires AllReady(os)
   requires forall oo <- os :: oo.Ready()
//requires pivot.Ready() //or not!
   ensures AllReady(os+{next})
   ensures flattenAllInside(os+{next}, pivot) == flattenAllInside(os,pivot) + collectAllInside(next,pivot)
   {
     assert forall x <- flattenAllInside(os+{next},pivot) ::
        || x in flattenAllInside(os,pivot)
        || x in collectAllInside(next,pivot);

    assert forall x <- flattenAllInside(os,pivot) + collectAllInside(next,pivot) ::
           x in flattenAllInside(os+{next},pivot);

   }







//opaque
predicate REQ_INSIDE(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner,
                  osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)
  reads m.hns()
{
    && (strictlyInside(next,m.o))    //should this be here or refactor?

    && (AllReady(oo))
    && (next.Ready())
    && (cext.Ready())
    && (klonReady(m))
    && (klonCalid(m))
    && (m.m.Keys >= flatten(oo) >= oo)
    && (oo     == todo + {next} + done)
    && (todo !! {next} !! done)
    && (next in m.m.Keys)
    && (cext == m.m[next])
    && (klonLine(next,cext,m))


    && (osp'    == obelow' + oabove' + opivot')
    && (osp'    == flatten(done))
    && (csp'    == cbelow' + cabove' + cpivot')
    && (csp'    == flatten(mapThruKlon(done, m)))

    && (obelow' == (set x <- osp' | strictlyInside(x,m.o)))
    && (cbelow' == (set x <- csp' | strictlyInside(x,m.c)))
    && (opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {}))
    && (cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {}))
    && (oabove' == fOutside(done-{m.o}, m.o))
    && (cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c))
    && (oabove' == cabove')

    && (obelow == obelow' + collectAllInside(next,m.o))
    && (cbelow == cbelow' + collectAllInside(cext,m.c))
    && (opivot == m.o.AMFO)
    && (cpivot == m.c.AMFO)
    && (oabove == oabove')
    && (cabove == cabove')


    // && (osp    == osp' + next.AMFO)
    // && (csp    == csp' + cext.AMFO)
    // && (osp    == flatten(done+{next}))
    // && (csp    == flatten(mapThruKlon(done+{next}, m)))
    //U3
    //  ensures obelow  == (set x <- osp | strictlyInside(x,m.o))
    //  ensures cbelow  == (set x <- csp | strictlyInside(x,m.c))
    //U4
    //  ensures oabove == fOutside((done+{next})-{m.o}, m.o)
    //  ensures cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c)

    && (osp    == obelow + oabove + opivot)
    && (csp    == cbelow + cabove + cpivot)
}
