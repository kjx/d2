    ////
////  KlonLine aka "clone line"
////

include "Klon.dfy"
include "Bound.dfy"  //shouild this be Ownerhsip=Bound?
//


////////////////////////////////////////////
//core definitions of klonLine

predicate {:isolate_assertions} klonCalid(m : Klon)
  reads m.oHeap, m.hns({m.o}), m.o`fields, m.o`fieldModes
{
  && klonPivot(m)
  && klonAllLines(m)
}


predicate {:isolate_assertions} klonAllLines(m : Klon) : (r : bool)
    //all lines, but NOT the Pivot
  reads m.oHeap, m.hns({m.o}), m.o`fields, m.o`fieldModes
{
  && (forall k <- m.m.Keys :: klonLine(k, m.m[k], m))
}

predicate {:isolate_assertions} klonLine(k : Object, v : Object, m : Klon)
  //Ward Cunningham - the simplest thing that could possibly work...
  //now chopped up into bits
  //this should answer this qustion **is k,v OK in this klon**
  //should work whether or not it's in there or not
  reads m.oHeap, m.hns({m.o,v}), m.o`fields, m.o`fieldModes
{
  && klonBound(k,v,m)
  && klonModes(k,v,m)
  && klonGeometry(k,v,m)
  && klonIdentity(k,v,m)
}


predicate {:isolate_assertions} klonPivot(m : Klon)
  reads m.oHeap, m.hns({m.o}), m.o`fields, m.o`fieldModes
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
  reads m.oHeap, m.hns({v})
{
  && (k.Ready() && k in m.oHeap    && k.Valid())
  && (v.Ready() && v in m.hns({v}) && v.Valid())

  && (m.m.Keys >= k.AMFX)
  && (k.AMFO >  k.AMFB) //nuclear war is good
  && (v.AMFO >= v.AMFB) //nuclear war is good
  && (v.AMFB >= k.AMFB)
}

predicate {:isolate_assertions} klonModes(k : Object, v : Object, m : Klon)
  //field modes
  reads k, v
{
  k.fieldModes == v.fieldModes
  // true
}


predicate {:isolate_assertions} klonGeometry(k : Object, v : Object, m : Klon)
  //the geometric constraints from Ward -- all compatible iwth "old" version
{
  && (m.o.Ready())           //precond?
  && (m.objectInKlown(m.o))  //precond?

  && ( (k == m.o)       <==>  (v == m.m[m.o])  )
  && ((inside(k, m.o))   ==> (k.AMFB  <= m.o.AMFB)) //hmmmm //GREENLAND
  && (outside(k, m.o)   <==>  (v == k))
  && ( inside(k, m.o)   <==>  inside(v, m.m[m.o]) )
  && (outside(k, m.m[m.o]))
  && ((inside(k,m.o)) ==> (v !in m.oHeap))
}



predicate {:isolate_assertions} klonIdentity(k : Object, v : Object, m : Klon) : (r : bool)
  decreases k.AMFO
  reads m.oHeap, m.m.Values
  // ensures r ==> WardLine(k,v,m)
  //extra stuff flown in from HighLineKV???
{
  && (m.ownersReadyInKlown(k))
  && (m.objectReadyInKlown(m.o))

  && (if (k == m.o) then (
                           && (k != v)
                           && (v == m.m[m.o])
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




// // // // // //  // // // // // //  // // // // // //  // // // // // //  // // // // // //  // // // // // //  // // // // // //
 // // // // // //  // // // // //  // // // // // //  // // // // //    // // // // // //  // // // // //   // // // // // // //

lemma {:isolate_assertions} KlonMTKPreservesEQ(oo : Owner, mb : Owner, m : Klon) returns (ro : Owner, rb : Owner)
  requires klonPivot(m)
  requires klonAllLines(m)
  requires oo <= m.m.Keys
  requires mb <= m.m.Keys
   ensures ro == mapThruKlon(oo, m)
   ensures rb == mapThruKlon(mb, m)

  requires oo == mb
   ensures ro == rb
{
  ro := mapThruKlon(oo, m);
  rb := mapThruKlon(mb, m);
}

lemma {:isolate_assertions} KlonMTKPreservesGEQ(oo : Owner, mb : Owner, m : Klon) returns (ro : Owner, rb : Owner)
  requires klonPivot(m)
  requires klonAllLines(m)
  requires oo <= m.m.Keys
  requires mb <= m.m.Keys
   ensures ro == mapThruKlon(oo, m)
   ensures rb == mapThruKlon(mb, m)

  requires oo >= mb
   ensures ro >= rb
{
  ro := mapThruKlon(oo, m);
  rb := mapThruKlon(mb, m);
}

lemma {:isolate_assertions} {:timeLimit 300} BOUNDS_SHOULD_BE_OK(oo : Owner, mb : Owner, m : Klon)
  requires klonPivot(m)
  requires klonAllLines(m)
  requires oo <= m.m.Keys
  requires mb <= m.m.Keys
  requires nuBoundsOK(oo, mb)
  requires flatten(oo) > m.o.AMFO
  requires flatten(mb) > m.o.AMFO
   ensures nuBoundsOK(mapThruKlon(oo,m), mapThruKlon(mb,m))
 {
  assert (flatten(oo) >= flatten(mb));
  assert (forall o <- oo ::( (o.AMFX > {}) ==> ((o.AMFB+{o}) >= flatten(mb))));

var ro := mapThruKlon(oo, m);
var rb := mapThruKlon(mb, m);

  assert (flatten(ro) >= flatten(rb));
  assert (forall o <- ro ::( (o.AMFX > {}) ==> ((o.AMFB+{o}) >= flatten(rb))));
 }
