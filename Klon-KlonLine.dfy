////
////  KlonLine aka "clone line"
////

include "Klon.dfy"
include "Bound.dfy"  //shouild this be Ownerhsip=Bound?
//


////////////////////////////////////////////
//core definitions of klonLine

predicate {:isolate_assertions}  klonReady(m : Klon) : (b : bool) ///like Ready, should be built in to the type
  //constant true facts about all Klons!
  reads {}
  ensures (m.m.Values <= m.hns())
  ensures b ==> (forall x <- m.hns() :: x.Ready())
  ensures b ==> AllReady(m.m.Values)
  {
    && (m.o in m.oHeap)    //need so we don't need a reads clause about m.o
    && (m.o.Ready())  // do we want Valid too?
    && (m.objectInKlown(m.o))
    && (m.m[m.o] == m.c)
    && (m.o.AMFX == m.o_amfx)
    && (m.o.AMFO == m.o_amfx+{m.o})
    && (m.clowner == m.c.owner)
    && (m.clbound == m.c.bound)
    && ((m.c.AMFX  == m.c_amfx))
    && ((m.c.AMFB  == m.c_amfb))
    && myBoundsOK(m.o.owner, m.o.bound) ///note - direct implementation is lurking below!?!
    // && (flatten(m.clbound) >= m.o.AMFB)  //WHAT THE FUCK?              ///      |
    && (m.oHeap >= m.c_amfx >= flatten(m.clbound) >= flatten(m.o.bound))  /// <----+

//following added in from the old apoCalidse()...
    && (m.m.Keys <= m.oHeap)
    && (m.m.Values <= m.hns())
    // && (m.objectReadyInKlown(o))   //this was originally two predicates
    && (forall x <- m.hns() :: x.Ready()) //whatt bno value owners ready??
    && (forall x <- m.m.Keys :: m.objectInKlown(x) && m.m[x].Ready())
    && (m.c_amfx <= m.oHeap)
  }

predicate {:isolate_assertions} klonCalid(m : Klon)
//  requires klonReady(m)  //?
  reads m.hns()
{
  && klonReady(m)
  && klonPivot(m)
  && klonAllLines(m)
  && klonHeap(m)
}

predicate {:isolate_assertions} klonHeap(m : Klon)
  requires klonReady(m)
  reads m.hns()
{
  && (forall x <- m.oHeap    :: x.Context(m.oHeap))
  && (forall x <- m.m.Values :: x.Context(m.hns()))
}


lemma WidenTheHeap(m : Klon)
  requires klonReady(m)
  requires forall x <- m.oHeap :: x.Context(m.oHeap)
   ensures forall x <- m.oHeap :: x.Context(m.hns())
{}

predicate {:isolate_assertions} klonAllLines(m : Klon) : (r : bool)
  requires klonReady(m)
  reads m.hns()
  {forall k <- m.m.Keys :: klonLine(k, m.m[k], m)}

predicate {:isolate_assertions} klonLine(k : Object, v : Object, m : Klon)
  //Ward Cunningham - the simplest thing that could possibly work...
  //now chopped up into bits
  //this should answer this qustion **is k,v OK in this klon**
  //should work whether or not it's in there or not
  requires klonReady(m)
  reads m.hns(), k, v
{
      && klonBound(k,v,m)
      && klonModes(k,v,m)
      && klonGeometry(k,v,m)
      && klonIdentity(k,v,m)
}


predicate {:isolate_assertions} klonPivot(m : Klon)
  requires klonReady(m)
 reads m.hns()
{
  && m.o.Valid() && m.o.Context(m.oHeap)
  && m.c.Valid() && m.c.Context(m.hns({m.c}))
}


predicate {:isolate_assertions} OLD_klonPivot(m : Klon)
  requires klonReady(m)
  reads m.hns()
{
  && (m.o.Ready() && m.o.Valid() && m.o.Context(m.oHeap) && m.objectInKlown(m.o))
  && (m.m[m.o] == m.c) && m.c.Valid() && m.c.Context(m.hns({m.c}))
  && nuBoundsOK(m.o.owner, m.o.bound)     // isn't tbis in READY
  && (m.o.AMFX == m.o_amfx)
  && (m.o.AMFO == m.o_amfx+{m.o})
  && (m.clowner == m.c.owner)
  && (m.clbound == m.c.bound)
  &&((m.c.AMFX  == m.c_amfx))
  &&((m.c.AMFB  == m.c_amfb))
  && myBoundsOK(m.o.owner, m.o.bound) ///note - direct implementation is lurking below!?!
  // && (flatten(m.clbound) >= m.o.AMFB)  //WHAT THE FUCK?              ///      |
  && (m.oHeap >= m.c_amfx >= flatten(m.clbound) >= flatten(m.o.bound))  /// <----+
}





predicate {:isolate_assertions} klonBound(k : Object, v : Object, m : Klon)
  requires klonReady(m)
  reads m.hns(), k, v
{
  && (k.Ready() && k in m.oHeap    && k.Valid() && k.Context(m.oHeap))
  && (v.Ready() && v in m.hns({v}) && v.Valid() && v.Context(m.hns({v})))

  && (m.m.Keys >= k.AMFX)
  && (k.AMFO   >  k.AMFB) //nuclear war is good
  && (v.AMFO   >= v.AMFB) //nuclear war is good
  && (v.AMFB   >= k.AMFB)
}

predicate {:isolate_assertions} klonModes(k : Object, v : Object, m : Klon)
  requires klonReady(m)
  reads m.hns(), k, v
  //field modes
  reads k, v
{
  k.fieldModes == v.fieldModes
  // true
}


predicate {:isolate_assertions} klonGeometry(k : Object, v : Object, m : Klon)
  //the geometric constraints -- all compatible iwth "old" version
  requires klonReady(m)
  reads m.hns(), k, v
{
  && (m.o.Ready())           //precond?
  && (m.objectInKlown(m.o))  //precond?

  && ( (k == m.o)       <==>  (v == m.c)  )
  && ((inside(k, m.o))   ==> (k.AMFB  <= m.o.AMFB)) //hmmmm //GREENLAND
  && (outside(k, m.o)   <==>  (v == k))
  && ( inside(k, m.o)   <==>  inside(v, m.c) )
  && (outside(k, m.c))
  && ((inside(k,m.o)) ==> (v !in m.oHeap))
}

lemma EXTRA_GEMO(k : Object, v : Object, m : Klon)
  requires klonReady(m)
  requires klonGeometry(k,v,m)
   ensures ( outside(k, m.o)   <==>  outside(v, m.c) )
{}

predicate {:isolate_assertions} klonIdentity(k : Object, v : Object, m : Klon) : (r : bool)
  requires klonReady(m)
  reads m.hns(), k, v
  {
  && (m.ownersReadyInKlown(k))
  && (m.objectReadyInKlown(m.o))

  && (if (k == m.o) then (
                           && (k != v)
                           && (v == m.c)
                           && (v.owner == m.clowner)
                           && (v.bound == m.clbound)

                         ) else if (outside(k, m.o) )
      then (
                          assert k != m.o;
                          k == v
     ) else (
          assert strictlyInside(k, m.o);
          assert k != m.o;
          && (k != v)
          && (v.bound == mapThruKlon(k.bound, m))
          && (v.owner == mapThruKlon(k.owner, m))
        ))
}



// // // // // //  // // // // // //  // // // // // //  // // // // // //  // // // // // //  // // // // // //  // // // // // /


lemma {:isolate_assertions} KlonReadyFromKV(m : Klon, m' : Klon, k : Object, v : Object)
  requires m.from(m')
  requires klonReady(m')

  requires k !in m'.m.Keys
  requires v !in m'.m.Values
  requires klonVMapOK(m'.m)
  requires klonCanKV(m', k, v)
  requires m == m'.(m:=vmapKV(m'.m,k,v))

   ensures (m.m.Keys - m'.m.Keys) == {k}
   ensures k in m'.oHeap
   ensures m.objectInKlown(k)

   ensures m.m.Values == m'.m.Values + {v}
   ensures m.hns() >= m'.hns() + {k, v}
//   ensures (m.hns() - m'.hns()) == {k, v}

   ensures klonReady(m)
   {
    KlonReadyFrom(m,m');
   }

lemma {:isolate_assertions} KlonReadyFrom(m : Klon, m' : Klon)
  requires klonReady(m')
  requires m.from(m')

  requires (m.m.Keys - m'.m.Keys) <= m'.oHeap
  requires forall x : Object <- (m.hns() - m'.hns())   :: x.Ready()
  requires forall x : Object <- (m.m.Keys - m'.m.Keys) :: m.objectInKlown(x)

   ensures klonReady(m)
  {
    assert
    && (m.o in m.oHeap)
    && (m.o.Ready())
    && (m.objectInKlown(m.o))
    && (m.m[m.o] == m.c)
    && (m.o.AMFX == m.o_amfx)
    && (m.o.AMFO == m.o_amfx+{m.o})
    && (m.clowner == m.c.owner)
    && (m.clbound == m.c.bound)
    && ((m.c.AMFX  == m.c_amfx))
    && ((m.c.AMFB  == m.c_amfb))
    && myBoundsOK(m.o.owner, m.o.bound) ///note - direct implementation is lurking below!?!
    // && (flatten(m.clbound) >= m.o.AMFB)  //WHAT THE FUCK?              ///      |
    && (m.oHeap >= m.c_amfx >= flatten(m.clbound) >= flatten(m.o.bound))  /// <----+
    && (m.c_amfx <= m.oHeap)
    ;

    assert m.oHeap == m'.oHeap; //from from
    assert (m.m.Keys - m'.m.Keys) <= m'.oHeap;
    assert forall x : Object <- (m.hns() - m'.hns())   :: x.Ready();
    assert forall x : Object <- (m.m.Keys - m'.m.Keys) :: m.objectInKlown(x);

    assert
    && (m.m.Keys <= m.oHeap)
    && (m.m.Values <= m.hns())
    && (forall x <- m.hns() :: x.Ready())
    && (forall x <- m.m.Keys :: m.objectInKlown(x))
     ;
  }


lemma {:isolate_assertions} KlonLineFrom(k : Object, v : Object, m : Klon, m' : Klon)
  //given klonLine(k,v,m') move to klonLine(k,v,m)
  requires klonReady(m')
  requires klonLine(k,v,m')

  requires klonReady(m)  //requires or ensures???
  requires m.from(m')
   ensures klonLine(k,v,m)
{
  assert klonBound(k,v,m')  ==> klonBound(k,v,m);
  assert klonModes(k,v,m')  ==> klonModes(k,v,m);
  assert klonGeometry(k,v,m')  ==> klonGeometry(k,v,m);

  KlonIdentityFrom(k,v,m,m');
  assert klonIdentity(k,v,m')  ==> klonIdentity(k,v,m);
}


lemma {:isolate_assertions} KlonIdentityFrom(k : Object, v : Object, m : Klon, m' : Klon)
  requires klonReady(m')
  requires klonIdentity(k,v,m')
  requires m.from(m')
  requires klonReady(m)
   ensures klonIdentity(k,v,m)
{ }



//
// lemma {:isolate_assertions} KLF_Line(m : Klon, m' : Klon)
//     requires klonReady(m')
//     requires klonCalid(m')
//      ensures klonAllLines(m')
//    requires m.from(m')
//
//
//   requires (m.m.Keys - m'.m.Keys) <= m'.oHeap
//   requires forall x : Object <- (m.hns() - m'.hns())       :: x.Ready()
//   requires forall x : Object <- (m.m.Keys   - m'.m.Keys)   :: m.objectInKlown(x)
//   requires forall x : Object <- (m.m.Keys   - m'.m.Keys)   :: klonLine(x,m.m[x],m')
//   requires forall x : Object <- (m.m.Values - m'.m.Values) :: x.Context(m.hns())
//
//      ensures klonReady(m)
//      ensures klonCalid(m)
//      ensures klonAllLines(m)
// {
//
//   forall x <- m.m.Keys ensures m.objectInKlown(x) //by
//   {
//     if (x in m'.m.Keys) {
//         assert m'.objectInKlown(x);
//         assert m'.bjectInKlown(x);
//         assert klonLine(x,m'.m[x],m');
//
//     } else {
//        assert x !in m'.m.Keys;
//        assert x  in  m.m.Keys;
//        assert x  in (m.m.Keys - m'.m.Keys);
//        assert m.objectInKlown(x);
//     }
//   }
// }


lemma {:isolate_assertions} KlonCalidFrom(m : Klon, m' : Klon)
  requires klonReady(m')
  requires klonCalid(m')

  requires m.from(m')

  requires (m.m.Keys - m'.m.Keys) <= m'.oHeap
  requires forall x : Object <- (m.hns() - m'.hns())       :: x.Ready()
  requires forall x : Object <- (m.m.Keys   - m'.m.Keys)   :: m.objectInKlown(x)
  requires forall x : Object <- (m.m.Keys   - m'.m.Keys)   :: klonLine(x,m.m[x],m')
  requires forall x : Object <- (m.m.Values - m'.m.Values) :: x.Context(m.hns())

   ensures klonReady(m)
   ensures klonCalid(m)
  {
    KlonReadyFrom(m, m');
    assert m.oHeap == m'.oHeap;

    assert
      && klonReady(m')
      && klonPivot(m')
      && klonAllLines(m')
      && klonHeap(m')
      ;

    assert (forall x : Object <- m'.m.Values :: x.Context(m.hns()));
    assert (forall x : Object <- (m.m.Values - m'.m.Values) :: x.Context(m.hns()));
    assert (m.m.Values - m'.m.Values + m'.m.Values) == m.m.Values;
    assert (forall x : Object  <- m.m.Values :: x.Context(m.hns()));


    assert
      && (forall x <- m.oHeap    :: x.Context(m.oHeap))
      && (forall x <- m.m.Values :: x.Context(m.hns()))
      ;

    assert (forall x : Object <- m'.m.Keys :: klonLine(x,m'.m[x],m'));
    assert (forall x : Object <- m'.m.Keys :: m.m[x] == m'.m[x]);
    assert (forall x : Object <- m'.m.Keys :: klonLine(x,m.m[x],m'));
    forall x : Object <- m'.m.Keys ensures (klonLine(x,m.m[x],m))  //by
      {
         assert klonLine(x,m.m[x],m');
            KlonLineFrom(x,m.m[x],m,m');
         assert klonLine(x,m.m[x],m);
      }

    assert (forall x : Object <- (m.m.Keys - m'.m.Keys) :: klonLine(x,m.m[x],m'));
    forall x : Object <- (m.m.Keys - m'.m.Keys) ensures (klonLine(x,m.m[x],m))  //by
      {
         assert klonLine(x,m.m[x],m');
            KlonLineFrom(x,m.m[x],m,m');
         assert klonLine(x,m.m[x],m);
      }

    assert (m.m.Keys - m'.m.Keys + m'.m.Keys) == m.m.Keys;
    assert (forall x : Object  <- m.m.Keys :: klonLine(x,m.m[x],m));

    assert
      && klonReady(m)
      && klonPivot(m)
      && klonAllLines(m)
      && klonHeap(m)
      ;
  }
















//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//
//=//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//=//
//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//====//

//
// lemma {:isolate_assertions} InternalOwnersWithinPivot(oo : Owner, bb : Bound, co : Owner, cb : Bound, m : Klon)
//   requires klonReady(m)
//   requires klonCalid(m)
//   requires AllReady(oo)
//   requires AllReady(bb)
//   requires AllReady(co)
//   requires AllReady(cb)
//
//   requires {} < oo <= m.m.Keys
//   requires bb <= m.m.Keys
//   requires co == mapThruKlon(oo, m)
//   requires cb == mapThruKlon(bb, m)
//
//   requires oo != bb
//   requires flatten(oo) >= flatten(bb)
//    ensures flatten(co) >= flatten(cb)
//    {
//    }




function {:isolate_assertions} InternalOwnersWithinPivot(o : Object, m : Klon) : Owner
  //recursivelylooks at all of o's owners that are inside m.o, classifying them as either
  requires klonReady(m)
  requires klonCalid(m)
  requires o.Ready()
  requires o in m.m.Keys
{
  {}
  //  if (inside(o,m.o))
  //    then (
  //     if (o == m.o) then ({},{},{o}) else
  //        o
  //    )
  //    else ({},{},{})
}





function {:isolate_assertions} {:timeLimit 10} internalOwners(o : Object, m : Klon) : Owner
  decreases allAMFOs({o}), 1
//      reads m.hns()
   requires klonReady(m)
   //requires klonCalid(m)
   requires o.Ready()
   requires o in m.m.Keys
   {
    if (strictlyInside(o,m.o))
      then ({o} +  internalFlatten(o.owner, m))
      else {}
   }

function {:isolate_assertions} {:timeLimit 10} internalFlatten(oo : Owner, m : Klon) : Owner
  //decreases allAMFOs(oo), 2
//      reads m.hns()
   requires klonReady(m)
  // requires klonCalid(m)
   requires forall o <- oo :: o.Ready()
   requires oo <= m.m.Keys
    {
     assert forall o <- oo :: o.Ready();
     assert forall o <- oo :: ( allAMFOs(oo) >= o.AMFO );

     assert forall o <- oo :: ( allAMFOs(oo) decreases to o.AMFO );
 //    assert forall o <- oo :: ( allAMFOs(oo), 2  decreases to  o.AMFO, 1 );

//  assert  allAMFOs(oo) decreases to allAMFOs(o.owner);
//  assert  allAMFOs({}) ,lts

     ( set o : Object <- oo, ooo <- internalOwners(o,m) :: ooo )
    }

//



function {:isolate_assertions} UNFINISHED_classifyOwnersWithin(o : Object, m : Klon) : (Owner, Owner, Owner)
  //looks at all of o's owners that are inside m.o, classifying them as either
   //- internal ---
   //- external --- outsife
  requires klonReady(m)
  requires klonCalid(m)
  requires o.Ready()
  requires o in m.m.Keys
{
   ( {}, {}, {} )
  //  if (inside(o,m.o))
  //    then (
  //     if (o == m.o) then ({},{},{o}) else
  //        o
  //    )
  //    else ({},{},{})
}