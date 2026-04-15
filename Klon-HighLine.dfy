include "Klon-Lemmata.dfy"

include "Library.dfy"

include "Klon-KlonLine.dfy"

  predicate {:isolate_assertions} HighCalidFragilistic(m : Klon) : (r : bool)
    requires m.apoCalidse()
    reads m.oHeap, m.hns()
     {
                && (forall k <- m.m.Keys :: HighLineKV(k, m.m[k], m))
     }


 predicate {:isolate_assertions} HighLineKV(k : Object, v : Object, m : Klon)
    requires m.apoCalidse()
    reads m.oHeap, m.hns()
  {
    && (k.Ready() && (m.ownersInKlown(k)) && k in m.oHeap)
    && (v.Ready() && (v in m.hns({v})))

    && (v.AMFO  >= v.AMFB  >= k.AMFB)


// here 'tis the final? clownership invariant!

    && ((inside(k, m.o)) ==> (k.AMFB  <= m.o.AMFB)) //hmmmm //GREENLAND

    && (outside(k, m.o)   <==>  (v == k))

       //doing it like this impliwes outside(k, m.o)  <==> outside(v, m.o)  ///EXCEPT NO IT DOESNT!!!
        //which is probalby too strong beecause it stops you cloning somethign to INSIDE ITSELF
        //i.e "moving down" which is a perfectly sensible thing to do.
        //perhaps have outgoing...

        //point is that v can be outside  m.o  but also  inside      m.c (inside m.m[m.o])
        //outgoing is outside both m.o and m.\c

    && ( inside(k, m.o)   <==>  inside(v, m.m[m.o]) )   //aka inside(k, m.o) <==>  inside(k, m.c)
          //or could be strictlyInside, but doesl't need to be?  (or preahps it DOES)

//    && ( strictlyInside(k, m.o)   <==>  strictlyInside(v, m.m[m.o])

    && ( (k == m.o)       <==>  (v == m.m[m.o])  )      //aka (k == m.o)  <==>  (v == m.c)

    && ( inside(k, m.o)   <==> (v !in m.oHeap))

    && (outside(k, m.m[m.o]))   //which should be OK even if inside(m.m[m.o], m.o)

//this needs to be added!!!
//   && (k.fieldModes  == v.fieldModes)

  //MAPPING - progFEARSATAN
    && (mappingOwnersThruKlownKV(k,v,m))
  }

lemma EstablishHighLineKV(k : Object, v : Object, m : Klon)

  //HighLineKV precondition
  requires m.apoCalidse()
  //HighLineKV body
  requires (k.Ready() && (m.ownersInKlown(k)) && k in m.oHeap)
  requires (v.Ready() && (v in m.hns({v})))
  requires (v.AMFO  >= v.AMFB  >= k.AMFB)
  requires ((inside(k, m.o)) ==> (k.AMFB  <= m.o.AMFB))
  requires (outside(k, m.o) <==>  (v == k))
  requires ( inside(k, m.o) <==>  inside(v, m.m[m.o]) )
  requires ( (k == m.o)     <==>  (v == m.m[m.o])  )
  requires ( inside(k, m.o) <==> (v !in m.oHeap))
  requires (outside(k, m.m[m.o]))
  requires (k.fieldModes   == v.fieldModes)
  requires (mappingOwnersThruKlownKV(k,v,m))
  //HighLineKV body
   ensures HighLineKV(k,v,m)
{}



lemma HighLineFrom(m : Klon, m' : Klon)
  requires m.from(m')
  requires m'.apoCalidse()
  requires m.m.Keys <= m.oHeap
  requires forall k <- m'.m.Keys :: k.Ready() && m.objectInKlown(k)
   ensures m .apoCalidse()
   ensures m'.m.Keys <= m.m.Keys

  requires forall k <- m'.m.Keys :: HighLineKV(k, m'.m[k], m')
   ensures forall k <- m'.m.Keys :: m.m[k] == m'.m[k]
   ensures forall k <- m'.m.Keys :: HighLineKV(k, m .m[k], m')
//   ensures forall k <- m'.m.Keys :: HighLineKV(k, m .m[k], m') ==> HighLineKV(k, m .m[k], m )

  ensures forall k <- m'.m.Keys :: HighLineKV(k, m .m[k], m )  //result
//   ensures forall k <- m'.m.Keys :: HighLineKV(k, m'.m[k], m )  //extra
{

forall k <- m'.m.Keys ensures (HighLineKV(k, m.m[k], m ))  //by
  {
    var v := m.m[k];  assert v == m'.m[k];
    assert HighLineKV(k,v,m');

    assert (k.Ready() && (m'.ownersInKlown(k)) && k in m'.oHeap);
    assert (v.Ready() && (v in m'.hns({v})));
    assert (v.AMFO  >= v.AMFB  >= k.AMFB);
    assert ((inside(k, m'.o)) ==> (k.AMFB  <= m'.o.AMFB));
    assert (outside(k, m'.o)   <==>  (v == k));
    assert ( inside(k, m'.o)   <==>  inside(v, m'.m[m'.o]) );
    assert ( (k == m'.o)       <==>  (v == m'.m[m'.o])  );
    assert ( inside(k, m'.o)   <==> (v !in m'.oHeap));
    assert (outside(k, m'.m[m'.o]));
    assert (mappingOwnersThruKlownKV(k,v,m'));

    if (k == m'.o) {
       assert (v == m'.m[m'.o]);
       assert (v.owner == m'.clowner);
       assert (v.bound == m'.clbound);
    }
    if ((k != m'.o) && outside(k, m'.o))  { assert k == v; }

    if (strictlyInside(k, m'.o)) {
       assert mappingOWNRsThruKlownKV(k.bound, v.bound, m');
       assert mappingOWNRsThruKlownKV(k.owner, v.owner, m');
    }
    assert mappingOwnersThruKlownKV(k,v,m');
    assert HighLineKV(k,v,m');
    ApoCalidseNow(m, m');


    assert (k.Ready() && (m.ownersInKlown(k)) && k in m.oHeap);
    assert (v.Ready() && (v in m.hns({v})));
    assert (v.AMFO  >= v.AMFB  >= k.AMFB);
    assert ((inside(k, m.o)) ==> (k.AMFB  <= m.o.AMFB));
    assert (outside(k, m.o)   <==>  (v == k));
    assert ( inside(k, m.o)   <==>  inside(v, m.m[m.o]) );
    assert ( (k == m.o)       <==>  (v == m.m[m.o])  );
    assert ( inside(k, m.o)   <==> (v !in m.oHeap));
    assert (outside(k, m.m[m.o]));

    if (k == m.o) {
       assert (v == m.m[m.o]);
       assert (v.owner == m.clowner);
       assert (v.bound == m.clbound);
    }
    if ((k != m.o) && outside(k, m.o))  { assert k == v; }

    if (strictlyInside(k, m.o)) {
        MappingOWNRsThruKlownKVFrom(k.bound, v.bound, m, m');
        MappingOWNRsThruKlownKVFrom(k.owner, v.owner, m, m');

        assert mappingOWNRsThruKlownKV(k.bound, v.bound, m);
        assert mappingOWNRsThruKlownKV(k.owner, v.owner, m);
    }

              // && (v.bound == mapThruKlon(k.bound, m))
              // && (v.owner == mapThruKlon(k.owner, m))


    assert mappingOwnersThruKlownKV(k,v,m);

    assert HighLineKV(k,v,m);

        }
}//End HighLineFrom





////////////////////////////////////////////////moveing aroudn to keep resolves quick
lemma ApoCalidseNow(m : Klon, m' : Klon)
  requires m.from(m')
  requires m'.apoCalidse()
  requires m.m.Keys <= m.oHeap
   ensures m .apoCalidse()
{
//commenting OR uncommenting these seems to make zero difference to the runtime!
//
    assert mapGEQ(m.m,  m'.m);
    assert m.o       == m'.o;
    assert m.clowner == m'.clowner;
    assert m.clbound == m'.clbound;
    assert m.oHeap   == m'.oHeap;
    assert m.o_amfx  == m'.o_amfx;
    assert m.c_amfx  == m'.c_amfx;

    assert (m'.m.Keys <= m'.oHeap);
    assert (m .m.Keys <= m .oHeap);
    assert (m'.m.Values <= m'.hns());
    assert (m .m.Values <= m .hns());
    assert (m'.objectReadyInKlown(m'.o));
    assert (m .objectReadyInKlown(m.o));
    assert (m'.HeapOwnersReady());
    assert (m .HeapOwnersReady());
    assert (m'.c_amfx <= m'.oHeap);
    assert (m .c_amfx <= m .oHeap);
}
////////////////////////////////////////////////moveing aroudn to keep resolves quick




lemma MappingOWNRsThruKlownKVFrom(kk : OWNR, vv: OWNR, m : Klon, m' : Klon)
  // so perish Unberlievers
  requires m.from(m')
  requires m'.apoCalidse()
  requires kk <= m'.m.Keys <= m'.oHeap <= m'.oHeap
  requires kk <= m.m.Keys              <= m.oHeap
   ensures m .apoCalidse()
  requires mappingOWNRsThruKlownKV(kk, vv, m')
   ensures mappingOWNRsThruKlownKV(kk, vv, m)
{}






//
//
//
// lemma {:isolate_assertions} HighCalidFromgalistic(k : Object, v : Object, m : Klon, m' : Klon)
//   requires HighCalidFragilistic(m')
//   requires k !in m'.m.Keys
//   requires v !in m'.m.Values
//
//   requires v.Ready()
//   requires v.Valid()
//   requires v.Context(m'.hns({v}))
//   requires (k.fieldModes == v.fieldModes)
//
//   ensures (
//   && klonVMapOK(m'.m) //BOWIE
//   && canVMapKV(m'.m, k, v)
//   && (k in m'.oHeap)  //prog do I want this here?
//   && (if (v==k) then (v in m'.oHeap) else (v !in m'.oHeap)) //nope - happens after  wards
//
//   //grrr. should refactor this
//   && k.Ready()
//   && k.Valid()
//   && k.Context(m'.oHeap)
//   && v.Ready()
//   && v.Valid()
//   && v.Context(m'.hns({v}))
//
//   //  && k.Context(m'.m.Keys+{k})  ///what IS this?
//   &&  m'.ownersInKlown(k)
//   && (k.fieldModes == v.fieldModes)//hhhmm see anbove
//     )
//   requires HighCalidFragilistic(m')  && HighCalidFragilistic(m) ///eeeeeeeeeevil time traveling spec...should be m'
//   requires m'.CKV_preconditions(k,v) && m.CKV_preconditions(k,v) ///eeeeeeeeeevil time traveling spec...should be m'
//   requires m'.apoCalidse()           && m.apoCalidse()       ///eeeeeeeeeevil time traveling spec...should be m'
//   requires m'.CalidLineKV(k,v)       && m.CalidLineKV(k,v) ///eeeeeeeeeevil time traveling spec...should be m'
//   requires HighLineKV(k,v,m')        && HighLineKV(k,v,m)   ///eeeeeeeeeevil time traveling spec...should be m'
//   requires m == m'.CalidKV(k,v)
//    ensures HighCalidFragilistic(m)
//    ensures HighLineKV(k,v,m)
//    {
//     assert HighCalidFragilistic(m');
//     assert m'.SuperCalidFragilistic();
//     assert klonVMapOK(m'.m);
//
//     assert HighLineKV(k,v,m');
//     HighLineFrom(m,m');
//     assert HighCalidFragilistic(m);
//     assert HighLineKV(k,v,m);
//
//     }
//
//
//
//
//
// predicate  {:isolate_assertions} SupaLine(k : Object, v : Object, m : Klon)
//  requires k.Ready()
//  requires v.Ready()
//  requires m.apoCalidse()
//  requires m.ownersInKlown(k)
//     reads m.oHeap, m.hns()
// {
//   && m.CalidLineKV(k,v)
//   && m.OwnersLineKV(k,v)
//   && HighLineKV(k,v,m)
// }
//
//  //see also
// lemma {:isolate_assertions} SupaDupa(k : Object, v : Object, m : Klon)
//  //hah hah hah - see alsoS uperDuperOwnerMapperKV
//  requires k.Ready()
//  requires v.Ready()
//  requires m.apoCalidse()
//  requires m.SuperCalidFragilistic() //computerOwnerForClone wants this
//  requires m.ownersInKlown(k)
// // requires strictlyInside(k, v)  //WHAT TBE FUCK IS THIS???
//  requires strictlyInside(k,m.o)
//   ensures strictlyInside(v,m.m[m.o])
//  requires SupaLine(k,v,m)   //needs one of thewse at least to verify
//   ensures mappingOwnersThruKlownKV(k,v,m)
//  // ensures v.owner == (mapThruKlon(k.owner, m))
//   ensures v.owner == (mapThruKlon(k.owner - m.o.AMFO, m) + m.m[m.o].AMFO)
//   ensures v.owner == (global(sideways(local(k.owner, m),m),m))
//   ensures v.owner == (shiftAMFOF(k.owner, m.o.AMFO,  m.m[m.o].AMFO, m.m))
//   ensures v.owner == computeOwnerForClone(k.owner, m)
//   {}
//
// lemma {:isolate_assertions} mTKshA(k : Object, v : Object, m : Klon)
//   requires k.owner <= m.m.Keys
//   requires k.owner >= m.o.AMFO
//   requires m.o in m.m.Keys
//
//   // requires v.owner == mapThruKlon(k.owner - m.o.AMFO, m) + m.m[m.o].AMFO
//   //  ensures v.owner ==   shiftAMFO(k.owner,  m.o.AMFO, m.m[m.o].AMFO, m.m)
//
//    ensures (mapThruKlon(k.owner - m.o.AMFO, m) + m.m[m.o].AMFO)
//            ==
//            (shiftAMFO(k.owner,  m.o.AMFO, m.m[m.o].AMFO, m.m))
//    {}
//
//
//
//    lemma ItMustBI(f : Object, t : Object, pivot : Object)
//      requires f.Ready() requires t.Ready() requires pivot.Ready()
//
//       requires strictlyInside(f, pivot)
//       requires outside(t, pivot)
//       requires refOK(f,t)
//
//       ensures f != t
//
//       ensures not( t.AMFO >= pivot.AMFO )
//       ensures f.AMFO >= pivot.AMFO
//       ensures not( t.AMFO >= f.AMFO)
//       ensures f !in t.owner
//       ensures not(refDI(f,t))
//
//       ensures refBI(f,t)
//       ensures (f.AMFB > {})
//       ensures (f.AMFB >=  t.AMFX)
//      { }
//
//
// lemma {:isolate_assertions} EverybodyHurts(k : Object, v: Object, m : Klon)
//   requires k.Ready() requires v.Ready()
//   requires m.objectInKlown(k)
//   requires m.m[k] == v
//   requires HighCalidFragilistic(m)
//
//   // ensures forall l <- m.m.Keys | (l.AMFO > m.o.AMFO) ==> (k.AMFO == l.AMFO) :: (v.AMFO == m.m[l].AMFO)
//   // ensures forall l <- m.m.Keys | (l.AMFO > m.o.AMFO) ==> (k.AMFO <  l.AMFO) :: (v.AMFO <  m.m[l].AMFO)
//   // ensures forall l <- m.m.Keys | (l.AMFO > m.o.AMFO) ==> (k.AMFO >  l.AMFO) :: (v.AMFO >  m.m[l].AMFO)
//   // ensures forall l <- m.m.Keys | (l.AMFO > m.o.AMFO) ==> (k.AMFO !! l.AMFO) :: (v.AMFO !! m.m[l].AMFO)
// {}
//
//     //  ensures forall l <- m.m.Keys ::
//   //          if (k.AMFO == l.AMFO) then (v.AMFO == m.m[l].AMFO)
//   //     else if (k.AMFO <  l.AMFO) then (v.AMFO <  m.m[l].AMFO)
//   //     else if (k.AMFO >  l.AMFO) then (v.AMFO >  m.m[l].AMFO)
//   //     else if (k.AMFO !! l.AMFO) then (v.AMFO !! m.m[l].AMFO)
//   //          else (true)
//
//   // ensures forall l <- m.m.Keys |  (k.AMFO == l.AMFO) :: (v.AMFO == m.m[l].AMFO)
//   // ensures forall l <- m.m.Keys |  (k.AMFO <  l.AMFO) :: (v.AMFO <  m.m[l].AMFO)
//   // ensures forall l <- m.m.Keys |  (k.AMFO >  l.AMFO) :: (v.AMFO >  m.m[l].AMFO)
//   // ensures forall l <- m.m.Keys |  (k.AMFO !! l.AMFO) :: (v.AMFO !! m.m[l].AMFO)
//
//
//
// lemma SetDJNZ<T>(a : set<T>, b : set<T>)
//   requires a > {}
//   requires b >= a
//    ensures b > {}
// {}
//
//
// lemma {:isolate_assertions} {:timeLimit 10} BoundsOfClone(oo : Owner, mb : Owner, m : Klon,
//                     ro : Owner, rb : Owner)
//     //see OwnershipOfCloneGEQ();
//     //see SuicideIsPainless
//     //NONE OF THEM WORK!!!
//   requires m.SuperCalidFragilistic()
//   requires m.apoCalidse()
//
//   requires flatten(oo) >= m.o.AMFO
//
//   requires oo <= m.m.Keys
//   requires mb <= m.m.Keys
//   requires flatten(oo) >= flatten(mb)
//   requires nuBoundsOK(oo,mb)
//
//   requires m.m.Values <= m.hns()
//   requires m.o.Ready()
//   requires m.objectInKlown(m.o)
//   requires m.HeapOwnersReady()
//   requires m.c_amfx <= m.oHeap
//
//   requires ro == mapThruKlon(oo, m)
//   requires rb == mapThruKlon(mb, m)
//
//   // requires ro == computeOwnerForClone(oo, m)
//   // requires rb == computeOwnerForClone(mb, m)
//
//   ensures nuBoundsOK(ro, rb)
//
// {
//   assert nuBoundsOK(oo,mb);
//
//
// //  OwnershipOfCloneGEQ2(flatten(oo), flatten(mb), m,  flatten(ro), flatten(rb));
//   // OwnershipOfCloneGEQ2((oo), (mb), m,  (ro), (rb));
//
//   assert flatten(mb) <= (set ooo <- oo, omb <- ooo.AMFB :: omb) + oo;
//
//   assert flatten(ro) >= flatten(rb);
//   assert flatten(mb) <= (set ooo <- oo, omb <- ooo.AMFB :: omb) + oo;
//
// }
//
//
//
//
//
//
//
//   lemma {:isolate_assertions}  RefOKGetsModeOK(source : Object, clone : Object, n : string, t : Object, u : Object, m : Klon)
//   //   //cloning source.Valid() && source.Context(context) results in clone.Valid() && clone.Context(context)
//   //was Birnamwood20
//   //9 Feb 2026
//     requires inside(source, m.o)   //note not strictly.
//     requires source.Ready()
//     requires source.Valid()   ///note this!1
//     requires clone.Ready()
//     requires t.Ready()
//     requires u.Ready()
//     requires m.objectInKlown(t)
//     requires m.objectInKlown(source)
//     requires m.apoCalidse()   ///note making a choice about what provision we need
//                              ///turning it on lets it work.
//     //  requires m.SuperCalidFragilistic()
//     //  requires HighLineCalid(m)
//         requires m.CalidOwners()
//
//
//     requires refOK(source, t)
//     requires refOK(clone, u)
//
//     requires m.objectInKlown(source)
//     requires clone == m.m[ source ]
//       requires n in source.fields.Keys
//       requires t == source.fields[n]
//       // requires n in clone.fields.Keys
//     requires n in source.fieldModes.Keys
//     requires n in  clone.fieldModes.Keys
//       // requires u == clone.fields[n]
//       // requires t in m.m.Keys
//       // requires u == m.m[ t ]
//
//     requires clone != source
//     requires outside(t, clone)  ///this is fine: the original.t can't be inside the clone...
//
//       // requires clone.fields[n] == m.m[ t ]
//       // requires clone.fields[n] == m.m[ source.fields[n] ]
//       // requires m.m[ source ].fields[n] == m.m[ source.fields[n] ]
//
// ///    requires source != m.o
//     requires inside(t,source) || outside(t,source) //colinearity?
//       //are we sure about that?
//
// //    requires strictlyInside(t, source) //hmm, should try with inside not strictlyInside?
//     requires m.ValuesOwnersReady()
//   ///NOOOO WRONG!  requires forall oo <- t.owner :: strictlyInside(oo, m.o)
//
//     requires modeOK(source, source.fieldModes[n], t) //YES THIS
//     requires source.fieldModes == clone.fieldModes //technically overkill...
//     requires source.fieldModes[n] == clone.fieldModes[n] //less overkill version
//
//
//     requires HighLineKV(t,u,m)
// //    requires mappingOWNRsThruKlownKV(t.owner, u.owner, m)  ///after the money's gone
//   //  requires mappingOwnersThruKlownKV(t,u,m);
//     // requires mappingOWNRsThruKlownKV(t.AMFO, u.AMFO, m)
//     // requires mappingOWNRsThruKlownKV(source.AMFO, clone.AMFO, m)
//     // requires mappingOWNRsThruKlownKV(source.AMFB, clone.AMFB, m)
//     // requires mappingOWNRsThruKlownKV(t.AMFX, u.AMFX, m)
//
// //    requires sameMode(source.fieldModes[n], clone.fieldModes[n])//9 Feb 2026
// //    requires sameRef(source, t, clone, u)
//      ensures modeOK(clone,  clone.fieldModes[n], u)
//   {
//     match (clone.fieldModes[n])
//         case Evil => assert modeOK(clone, clone.fieldModes[n], u);
//         case Rep | Owned(_) | Loaned(_) =>
//                assert refDI(source,t);
//                assert source in t.owner;
//                assert clone  in u.owner;
//                assert refDI(clone,u);
//                assert modeOK(clone, clone.fieldModes[n], u);
//         case Peer =>
//                //assert refBI(source,t);
//                assert mappingOwnersThruKlownKV(source, clone, m);
//                assert mappingOwnersThruKlownKV(t, u, m);
//                assert source.owner == t.owner;
//                assert m.apoCalidse();
//                assert source.owner <= m.m.Keys;
//                if (inside(t,source))
//                   {
//                       assert t.owner == m.o.owner == source.owner;
//                       assert clone.owner == m.clowner;
//                       assert inside(u, clone);
//                       assert mappingOWNRsThruKlownKV(source.owner, clone.owner, m);
//                       assert mappingOWNRsThruKlownKV(t.owner, u.owner, m);
//                       assert clone.owner == u.owner;
//                       assert modeOK(clone, clone.fieldModes[n], u);
//                   } else {
//                      assert t == u;
//                      assert refBI(source, t);
//                      assert refBI(clone, u);
//                      assert modeOK(clone, clone.fieldModes[n], u);
//                   }
//                assert modeOK(clone, clone.fieldModes[n], u);
//         case Borrow(_,_,_,_) =>
//                assert refOK(source,t);
//                assert (source==t) || refBI(source,t) || refDI(source,t);
//                assert (source==t) ==> (clone==u);
//                assert refBI(source,t)  ==> refBI(clone, u);
//                assert refDI(source,t)  ==> refDI(clone, u);
//                assert (clone==u)  || refBI(clone, u) || refDI(clone, u);
//                assert refOK(clone, u);
//                assert modeOK(clone, clone.fieldModes[n], u);
//         case Self =>
//                assert source == t;
//                assert  clone == u;
//                assert modeOK(clone, clone.fieldModes[n], u);
//     }
//
//   lemma {:isolate_assertions} FUCKERRefOKGetsModeOK(source : Object, clone : Object, n : string, t : Object, u : Object, m : Klon)
//   //   //cloning source.Valid() && source.Context(context) results in clone.Valid() && clone.Context(context)
//   //was Birnamwood20
//     requires strictlyInside(source, m.o)
//     requires source.Ready()
//     requires source.Valid()   ///note this!1
//     requires clone.Ready()
//     requires t.Ready()
//     requires u.Ready()
//     requires m.objectInKlown(t)
//     requires m.objectInKlown(source)
//     //  requires m.apoCalidse()
//     //  requires m.SuperCalidFragilistic()
//     requires m.CalidOwners()
//
//     requires refOK(source, t)
//     requires refOK(clone, u)
//
//     requires m.objectInKlown(source)
//     requires clone == m.m[ source ]
//       requires n in source.fields.Keys
//       requires t == source.fields[n]
//       // requires n in clone.fields.Keys
//     requires n in source.fieldModes.Keys
//     requires n in  clone.fieldModes.Keys
//       // requires u == clone.fields[n]
//       // requires t in m.m.Keys
//       // requires u == m.m[ t ]
//
//     requires clone != source
//     requires outside(t, clone)  ///this is fine: the original.t can't be inside the clone...
//
//       // requires clone.fields[n] == m.m[ t ]
//       // requires clone.fields[n] == m.m[ source.fields[n] ]
//       // requires m.m[ source ].fields[n] == m.m[ source.fields[n] ]
//
//     requires source != m.o
//     requires inside(t,source) || outside(t,source) //colinearity?
//
//     requires strictlyInside(t, source) //hmm, should try with inside not strictlyInside?
//     requires m.ValuesOwnersReady()
//     requires forall oo <- t.owner :: strictlyInside(oo, m.o)
//
//     requires source.fieldModes == clone.fieldModes
//     requires modeOK(source, source.fieldModes[n], t)
//
//     requires mappingOWNRsThruKlownKV(t.AMFO, u.AMFO, m)
//     requires mappingOWNRsThruKlownKV(source.AMFO, clone.AMFO, m)
//     requires mappingOWNRsThruKlownKV(source.AMFB, clone.AMFB, m)
//     requires mappingOWNRsThruKlownKV(t.AMFX, u.AMFX, m)
//
// //anoher weird yhing.  what's wrong with equals?
//     //  ensures sameMode(source.fieldModes[n], clone.fieldModes[n])//9 Feb 2026
// //    requires sameRef(source, t, clone, u)
//      ensures modeOK(clone,  clone.fieldModes[n], u) //** 24Sept
//     {
//     }
//
// //
// //
// // lemma LoudIsMoreGood(o : Object, m : Klon)
// //   requires o.Ready()
// //   requires HighCalidFragilistic(m)
// //    ensures
//
//
//
//  lemma {:isolate_assertions} CalidKVFromHighLineKV(k : Object, v : Object, m : Klon)
//    requires m.apoCalidse()
//    requires m.SuperCalidFragilistic()
//    requires HighCalidFragilistic(m)
//    requires HighLineKV(k,v,m)
//     ensures m.CalidLineKV(k,v)
//     {}
//
//
//
// lemma {:isolate_assertions} NuBoundsOfClone(k : Object, rowner : Owner, rbound : Owner, m : Klon)
//   requires m.apoCalidse()
//   requires m.SuperCalidFragilistic()
//   requires k.Ready()
//    ensures nuBoundsOK(k.owner, k.bound)  //paranoia, follows from Ready()
//   requires strictlyInside(k, m.o)
//
//   requires m.objectInKlown(k)
//   requires rowner == computeOwnerForClone(k.owner, m)
//    ensures rowner == (set x <- (k.owner - m.o.AMFO) :: m.m[x]) + m.m[m.o].AMFO
//   requires rbound == computeOwnerForClone(k.bound, m)
//    ensures rbound == (set x <- (k.bound - m.o.AMFO) :: m.m[x]) + m.m[m.o].AMFO
//
//    ensures nuBoundsOK(rowner, rbound)
//    {
//
// OwnershipOfCloneGEQ(flatten(k.owner), flatten(k.bound), m);
//
// assert flatten(rowner) >= flatten(rbound);
//
// assert flatten(k.bound) <= (set ooo <- k.owner, omb <- ooo.AMFB :: omb) + k.owner;
//
// assert flatten(rbound) <= (set ooo <- rowner, omb <- ooo.AMFB :: omb) + rowner;
//
//    }
//
//
// lemma {:isolate_assertions} {:timeLimit 60} ToHopeForDespair(oo : Owner, ob : Owner, ro : Owner, rb : Owner, m : Klon)
//   requires m.apoCalidse()
//   requires m.SuperCalidFragilistic()
//
//   requires forall k <- m.m.Keys ::  (strictlyInside(k, m.o)   <==>  strictlyInside(m.m[k], m.m[m.o]))  //seems kinda obvious...-- HighLineKV to Calid
//
//   requires AllReady(oo)
//   requires AllReady(ob)
//   requires AllReady(ro)
//   requires AllReady(rb)
//
//   requires oo <= m.m.Keys
//   requires ob <= m.m.Keys
//
//   requires forall o <- oo :: o.Ready() && m.objectInKlown(o)
//   requires forall o <- ob :: o.Ready() && m.objectInKlown(o)
//
//   requires ro == computeOwnerForClone(oo, m)
//   requires rb == computeOwnerForClone(ob, m)
//
//    ensures ro == (set x <- (oo - m.o.AMFO) :: m.m[x]) + m.m[m.o].AMFO      //I thought this was OK?
//    ensures rb == (set x <- (ob - m.o.AMFO) :: m.m[x]) + m.m[m.o].AMFO //and this one too?
//
//   requires flatten(oo) >= m.o.AMFO
//   requires nuBoundsOK(oo,ob)
// //   ensures nuBoundsOK(ro,rb)
//    ensures flatten(oo) >= flatten(ob)
// //   ensures flatten(ro) >= flatten(rb)
//  {
//    assert flatten(oo)            >= flatten(ob);
//    assert flatten(oo - m.o.AMFO) >= flatten(ob - m.o.AMFO);
//    var local_oo := (oo - m.o.AMFO);
//    var local_ob := (ob - m.o.AMFO);
//    assert flatten(local_oo) >= flatten(local_ob);
//
//
//   MapThruKlonGEQ( flatten(local_oo), flatten(local_ob), m );
//
// // SetMinusMapPlus(oo,ro,ob,rb,m.o.AMFO,m.m[m.o].AMFO,m);
//
// // assert flatten(set x <- local_oo :: m.m[x]) >= flatten(set x <- local_ob :: m.m[x]);
//
// //   assert flatten(mapThruKlon(local_oo, m)) >= flatten(mapThruKlon(local_ob, m));
//
//    var sideways_oo := mapThruKlon(local_oo, m);
//    var sideways_ob := mapThruKlon(local_ob, m);
// //   assert flatten(sideways_oo) >= flatten(sideways_ob);
//
//  }
//
// //  : flatten(mb) <= (set ooo <- oo, omb <- ooo.AMFB :: omb) + oo
// // This is the only assertion in batch #4 of 314 in method ToHopeForDespair
// // Batch #4 resource usage: 43.0M RU
// //
// // Error: a postcondition could not be proved on this return path
// // Inside nuBoundsOK(ro,rb)
// // Could not prove: flatten(oo) >= flatten(mb)
//
//
//
//
// lemma {:isolate_assertions} {:timeLimit 60} XX_Unused_ButWouldBeNice_TheresSomethingAboutSets(oo : Owner, ob : Owner, ro : Owner, rb : Owner, m : Klon)
//     requires m.o.Ready()
//     requires m.objectInKlown(m.o)
//     requires m.m.Keys >= oo
//     requires m.m.Keys >= ob
//     requires flatten(ob) >= m.o.AMFO
//     requires ro == (set x <- (oo - m.o.AMFO) :: m.m[x]) + m.m[m.o].AMFO
//     requires rb == (set x <- (ob - m.o.AMFO) :: m.m[x]) + m.m[m.o].AMFO
//     requires flatten(oo) >= flatten(ob)
//      ensures flatten(ro) >= flatten(rb)
//   {}
//
//
// lemma Corbyn(a : Owner, b : Owner, c : Owner, d : Owner)
//    requires flatten(a + b)  >= flatten(a + c)
// //    ensures flatten(b)      >= flatten(c)
//    {
//     assert flatten(a + b)  >= flatten(a + c);
//     assert flatten(a) + flatten(b) == flatten(a + b);
//     assert flatten(a) + flatten(c) == flatten(a + c);
//    }
//
//
//
// lemma XX_Unused_ButWouldBeNice_MapThruKlonFlatGEQFlat(os: set<Object>, ot : set<Object>,  m : Klon)
// //pity this doesn't work...
// //see  XX_Unused_ButWouldBeNice_TheresSomethingAboutSets above
//   requires os <= m.m.Keys
//   requires ot <= m.m.Keys
// // requires forall o <- os :: o.AMFO  > m.o.AMFO
//   requires flatten(os) >= flatten(ot)
//    ensures flatten(mapThruKlon(os, m)) >= flatten(mapThruKlon(ot, m))
// {
// }






//moved into class
// function boundForChildren(o : Object) : Bound
//  {
//   if (o.AMFB == o.AMFX) then (o.self) else (o.bound)
//  }


lemma {:isolate_assertions} BOUNDS_ALL_GOOD_TOO(k : Object, v : Object, m : Klon)
  decreases k.AMFO
  requires k.Ready()
  requires v.Ready()
  requires m.c.Ready()
  requires m.objectInKlown(k)
  requires klonLine(k,v,m)
   ensures klonPivot(m)
   ensures klonIdentity(k,v,m)
   ensures owner_of_clone(k,m) == v.owner
{}






lemma {:isolate_assertions} its_all_good_mate(k : Object, v : Object, m : Klon)
  decreases k.AMFO
  requires k.Ready()
  requires v.Ready()
  requires m.c.Ready()
  requires m.objectInKlown(k)
  requires klonLine(k,v,m)
   ensures klonPivot(m)
   ensures klonIdentity(k,v,m)
   ensures owner_of_clone(k,m) == v.owner
{
  if (k == m.o) {
        assert v == m.c;
        assert v.owner == m.clowner;
        assert v.owner == owner_of_clone(k,m);
        return;
  }

  if (outside(k, m.o)) {
      assert outside(v, m.c);
      assert k == v;
      assert v.owner == k.owner == owner_of_clone(k,m);
      return;
  }

  if (strictlyInside(k, m.o)) {
      // assert inside(k,m.o);
      // assert inside(v,m.c);
      // assert k != m.o;
      // assert v != m.c;
      // assert inside(v,m.c) && v != m.c;
      // v.ExtraReady();
      assert strictlyInside(v, m.c);
      assert v.owner == owner_of_clone(k,m);
      return;
  }


  assert false;
}


lemma {:isolate_assertions} strictly_ballroom(v : Object, m : Klon)
  requires klonPivot(m)
  requires v.Ready()
  requires m.c.Ready()
  requires inside(v,m.c)
  requires v != m.c
   ensures strictlyInside(v, m.c)
   {
    assert inside(v,m.c);
    assert v.AMFO >= m.c.AMFO;
    assert v != m.c;
    assert v.AMFO > m.c.AMFO;
    assert strictlyInside(v, m.c);
   }

function {:isolate_assertions} owner_of_clone(k : Object, m : Klon) : (vo : Owner)
  requires k.Ready()
  requires m.objectInKlown(k)
{
    if (k == m.o) then ( m.clowner )
     else if (outside(k, m.o)) then ( k.owner )
     else mapThruKlon(k.owner, m)
}



function {:isolate_assertions} AMFO_of_clone(k : Object, m : Klon) : (vo : OWNR)
  requires k.Ready()
  requires m.objectInKlown(k)
{
    if (k == m.o) then ( m.c_amfx )
     else if (outside(k, m.o)) then ( k.AMFX )
     else flatten(mapThruKlon(k.owner, m))
}


lemma {:isolate_assertions} MAP_THRU_IDS(os: set<Object>, m : Klon)
   requires os <= m.m.Keys
   requires forall x <- os :: m.m[x] == x
    ensures mapThruKlon(os,m) == os
    { }


lemma {:isolate_assertions} MAP_ONE(k : Object, v : Object, m : Klon)
   requires k in m.m.Keys
   requires m.m[k] == v
    ensures mapThruKlon({k},m) == {v}
    { }


lemma SUB_DISJ<T>(a : set<T>, b : set<T>)
   requires a !! b
    ensures a - b == a
{}

lemma FLAT_ONE(a : Object)
  requires a.Ready()
  requires flatten({a}) == a.AMFO
{}


lemma {:isolate_assertions} {:timeLimit 20} RefOKDI(f' : Object, t' : Object, f : Object, t : Object, m : Klon)
 requires f'.Ready()
 requires t'.Ready()
 requires f.Ready()
 requires t.Ready()
 requires m.objectInKlown(f')
 requires m.objectInKlown(t')
//  requires m.SuperCalidFragilistic()
//  requires HighCalidFragilistic(m)
 requires refDI(f',t')
 requires refOK(f',t')

  requires klonCalid(m)
  requires allKlonLines(m)
//  requires m.CalidLineKV(f', f)
//  requires m.CalidLineKV(t', t)
//  requires HighLineKV(f', f, m)
//  requires HighLineKV(t', t, m)

  //i.e thees are ACTUAL CLONES not POTENTIAL CLONES
 requires f == m.m[f']
 requires t == m.m[t']

//YET MORE FFECKING CASES cos SubAMFOsGeq is more restrictive
 requires inside(f', m.o)
 requires strictlyInside(t', m.o)
  // ensures refDI(f,t)
  // ensures refOK(f,t)
{
  assert refDI(f',t');
    assert t'.owner == {f'};
//  assert flatten({f'}) == flatten(t'.owner);
//  assert f'.self == t'.owner;
//  assert f'.AMFO == t'.AMFX;
  // assert f'.AMFO == (t'.AMFO - {t'});
  // assert (t'.AMFO - {t'}) == t'.AMFX;

  assert f == m.m[f'];
  assert t == m.m[t'];

//  assert m.CalidLineKV(f', f);
//  assert m.CalidLineKV(t', t);
//  assert HighLineKV(f', f, m);
//  assert HighLineKV(t', t, m);
//  assert mappingOwnersThruKlownKV(f', f, m);
//  assert mappingOwnersThruKlownKV(t', t, m);


// assert klonLine(f',f,m);
// assert klonLine(t',t,m);
// assert strictlyInside(f', m.o);
// assert strictlyInside(t', m.o);

//assert mappingOWNRsThruKlownKV(t'.owner, t.owner, m);

assert klonIdentity(t',t,m);
assert t.owner == mapThruKlon(t'.owner, m);

//  assert t .owner == mapThruKlon(t'.owner - m.o.AMFO, m) + m.c.AMFO;
////HAK  assert t'.owner == {f'};

  // assert flatten({f'}) == flatten(t'.owner);
  // assert f'.AMFO == t'.AMFX;


  // assert t .owner == mapThruKlon({f'}      - m.o.AMFO, m) + m.c.AMFO;
  // assert ({f'} - m.o.AMFO) == {f'}
  //  by {
  //       assert strictlyInside(f', m.o);
  //       assert {f'} !! m.o.AMFO;
  //       SUB_DISJ({f'}, m.o.AMFO);
  //       assert {f'} -  m.o.AMFO == {f'};
  //  }
////HAK  assert t .owner == mapThruKlon({f'}, m) + m.c.AMFO;
//  assert mapThruKlon({f'}, m) == set x <- {f'} :: m.m[x];
  assert m.m[f'] == f;
  MAP_ONE(f', f, m);
  assert mapThruKlon({f'}, m) == {f};
//  assert (set x <- {f'} :: m.m[x]) == {f};
//  assert mapThruKlon({f'}, m) == {f};
////HAK  assert t .owner == {f} + m.c.AMFO;

assert t.owner == {f};
//
// assert t.owner == {f} + m.c.AMFO;
// assert inside(f, m.c);
// ////HAK assert m.c.AMFO == flatten({m.c});
// assert flatten({f}) >= flatten({m.c});
// ////HAK assert flatten({f}) == flatten({f} + m.c.AMFO);
// assert flatten(t.owner) == flatten({f});

// assert {f} == computeOwnerForClone({f'}, m);
// assert {t} == computeOwnerForClone({t'}, m);

//   assert t'.owner == {f'};
//   assert t .owner == {f };
//
  assert refDI(f,t);
  assert refOK(f,t);


}







lemma {:isolate_assertions}  AMFO_PIVOT(k : Object, v : Object, m : Klon)
  requires k.Ready()
  requires v.Ready()
  requires m.objectInKlown(k)
  requires m.SuperCalidFragilistic()
  requires HighCalidFragilistic(m)
  requires HighLineKV(k,v,m)
  requires k == m.o
      ensures v == m.c
      ensures v.owner == m.clowner
      ensures v.AMFX  == flatten(m.clowner)
      ensures v.AMFO  == m.c_amfx + {m.c}
{}


lemma {:isolate_assertions} {:timeLimit 40} MAP_THRU_IDENTITY_SET(ks : Owner, m : Klon)
   requires AllReady(ks)
   requires ks <= m.m.Keys
   requires m.SuperCalidFragilistic()
   requires HighCalidFragilistic(m)
   requires forall x <- ks :: m.m[x] == x
    ensures ks == set x <- ks :: x
    ensures ks == set x <- ks :: m.m[x]
    ensures (set x <- ks :: x) == (set x <- ks :: m.m[x])
{}

//{:timeLimit 60}
lemma {:isolate_assertions} {:timeLimit 60} AMFO_OUTSIDE(k : Object, v : Object, m : Klon)
  requires k.Ready()
  requires v.Ready()
  requires m.objectInKlown(k)
  requires m.SuperCalidFragilistic()
  requires HighCalidFragilistic(m)
  requires HighLineKV(k,v,m)
  requires outside(k, m.o)
   ensures k == v
   ensures k.owner == v.owner
   ensures k.AMFO  == v.AMFO
//             ensures v.AMFO  == mapThruKlon(k.AMFO,m)
{
   assert k.AMFO <= m.m.Keys;
   assert forall x <- k.AMFO :: outside(x, m.o);
   assert forall x <- k.AMFO :: m.m[x] == x;
   assert k.AMFO == (set x <- k.AMFO :: x);
   assert (set x <- k.AMFO :: x) == (set x <- k.AMFO :: m.m[x]);
   assert (set x <- k.AMFO :: m.m[x]) == v.AMFO;
}

predicate effectivelyDirectlyInside(part : Object, whole : Object)
 {
  && part.Ready()
  && whole.Ready()
  && part.AMFX == whole.AMFO  //haw h aw haw
 }


lemma  {:isolate_assertions} {:timeLimit 7} AXIOM_DI(part : Object, whole : Object)
 requires part.Ready()
 requires whole.Ready()
 requires part.AMFX == whole.AMFO
  ensures whole in part.owner
  ensures forall p <- part.owner :: inside(whole, p)
  ensures forall p <- part.owner :: p in whole.AMFO

//  ensures part.owner == whole.self // can't have this, because
// part.owner can have any other flattened owner of whole in it
// semanticlaly the same as just having whole.  but...
{
  assert flatten(part.owner) == part.AMFX;
  assert flatten(whole.self) == flatten(whole.owner + {whole}) == whole.AMFO;
  assert flatten(part.owner) == flatten(whole.self);
  assert flatten(part.owner) == flatten(whole.owner + {whole});
  assert whole in part.owner;

  AXIOMAMFODIRECT(part, whole);
  assert forall p <- part.owner :: inside(whole, p);


}


lemma  {:isolate_assertions} {:timeLimit 7}  InsideIsInside(k : Object, v : Object, m : Klon)
  requires k.Ready()
  requires v.Ready()
  requires m.objectInKlown(k)
  requires m.SuperCalidFragilistic()
  requires HighCalidFragilistic(m)
  requires HighLineKV(k,v,m)
  requires inside(k, m.o)
   ensures inside(v, m.c)
   ensures strictlyInside(k,m.o) <==> strictlyInside(v,m.c)
   {}


lemma  {:isolate_assertions} {:timeLimit 30}   RefOKisRefOK(f' : Object, t' : Object, f : Object, t : Object, m : Klon)
   // Heap if RefiOJ then clone is REFOK
   // note this only works for Refs what are inside m.o
 requires f'.Ready()
 requires t'.Ready()
 requires f.Ready()
 requires t.Ready()
 requires m.objectInKlown(f')
 requires m.objectInKlown(t')
 requires m.SuperCalidFragilistic()
 requires HighCalidFragilistic(m)
 requires refOK(f',t')
 requires m.CalidLineKV(f', f)
 requires m.CalidLineKV(t', t)
 requires HighLineKV(f', f, m)
 requires HighLineKV(t', t, m)

  //i.e thees are ACTUAL CLONES not POTENTIAL CLONES
 requires f == m.m[f']
 requires t == m.m[t']


//YET MORE FFECKING CASES cos SubAMFOsGeq is more restrictive
 requires inside(f', m.o)
 requires strictlyInside(t', m.o)
//   ensures inside(f, m.m[m.o])
//   ensures strictlyInside(t, m.m[m.o])
//
//   ensures HighLineKV(f', f, m)
//   ensures HighLineKV(t', t, m)
//
//   ensures mappingOwnersThruKlownKV(f', f, m)
//   ensures mappingOwnersThruKlownKV(t', t, m)
//
//   ensures m.SuperCalidFragilistic()
//   ensures m.m.Keys >= f'.AMFB
//
// ensures refOK(f,t)
  {
assert  refOK(f',t');

assert t' != m.o;
assert t'.AMFO > m.o.AMFO;
assert mappingOwnersThruKlownKV(t', t, m);
assert mappingOWNRsThruKlownKV(t'.owner, t.owner, m);
assert t.owner == (mapThruKlon(t'.owner - m.o.AMFO, m) + m.m[m.o].AMFO);
// assert t.owner == shiftAMFO(t'.owner, m.o.AMFO, m.m[m.o].AMFO, m.m);
if (f' in t'.owner)  { assert f in t.owner; }


    if (f' == t')
     {
      assert f==t;
      return;
     }

    if (refBI(f',t'))
     {
      // assert f'.AMFB >= t'.AMFX;  //GREENLAND
      // assert f.AMFB  >= t.AMFX;  //GREENLAND

      assert (f'.AMFB > {}) && (f'.AMFB >=  t'.AMFX);
      assert (f'.AMFB > {});
      assert (f'.AMFB >= t'.AMFX);


  SubAMFOsGeq(f'.AMFB, t'.AMFX, f.AMFB, t.AMFX, m);
      assert (f .AMFB >=  t .AMFX);
      assert (f .AMFB > {});
      assert refBI(f,t);

      return;
     }

    if (refDI(f',t'))
     {
//
//
// print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";
// print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";
// print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";

  assume klonCalid(m);
  assume allKlonLines(m);

// print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";
//   print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";print "FUCK FUCK FUCK\n";


    RefOKDI(f',t',f,t,m);
///////////////////////////////////////////////////////////////////////////
//       // assert f' in t'.owner;  //AMDI_FINT //GREENLAND
//       assert f'.AMFO == t'.AMFX;
//       assert flatten(f'.owner + {f'}) == f'.AMFO;
//       assert flatten(t'.owner) == t'.AMFX;
//       assert flatten(f'.owner + {f'}) == flatten(t'.owner);
//       assert (f'.owner + {f'}) == t'.owner;
//
//       assert flatten(f'.owner) == f'.AMFX;
//       assert flatten(f'.self ) == f'.AMFO;
//       assert flatten(t'.owner) == t'.AMFX;
//       assert flatten(t'.self ) == t'.AMFO;
//
//       assert flatten(f'.self) == flatten(t'.owner);
// //      AXIOMAMFOS();
//       assert f'.self == t'.owner;
//
//       if (f' == m.o) {
//         //give up for now!!
//           assert f'.AMFO == m.o.AMFO;
//           assert f .AMFO == m.c.AMFO;
//           assert t'.AMFX == m.o.AMFO;
//           assert flatten(t'.owner) == t'.AMFX;
//           assert flatten(t'.owner) + {t'} == t'.AMFO;
//           assert flatten(t'.owner + {t'}) == t'.AMFO;
//
//           assert flatten(f'.owner) + {f'} == f'.AMFO;
//
//       assert m.CalidLineKV(t',t);
//       assert mappingOwnersThruKlownKV(t', t, m);
//       assert mappingOWNRsThruKlownKV(t'.bound, t.bound, m);
//       assert mappingOWNRsThruKlownKV(t'.owner, t.owner, m);
//       assert t.owner == mapThruKlon(t'.owner - m.o.AMFO, m) + m.c.AMFO;
//       assert flatten(t'.owner) == t'.AMFX;
//       assert flatten(t .owner) == t .AMFX;
//       assert t.owner == mapThruKlon(t'.owner - m.o.AMFO, m) + m.c.AMFO;
//       assert flatten(t.owner) == t.AMFX;
//
//
//       assert m.CalidLineKV(f',f);
//       assert mappingOwnersThruKlownKV(f', f, m);
//       assert mappingOWNRsThruKlownKV(f'.bound, f.bound, m);
//       assert mappingOWNRsThruKlownKV(f'.owner, f.owner, m);
//       assert f.owner == mapThruKlon(f'.owner - m.o.AMFO, m) + m.c.AMFO;
//       assert inside(f', m.o);
//       assert flatten(f'.owner + {f'}) == f'.AMFO;
//       assert flatten(f'.owner) == f'.AMFX;
//       assert f'.AMFO == t'.AMFX;
//       assert f.owner == mapThruKlon(f'.owner - m.o.AMFO, m) + m.c.AMFO;
//
//
//
//
//           assert t .AMFX == m.c.AMFO;
//           assert f .AMFO == m.c.AMFO == t .AMFX;
//
//           assert refDI(f',t');
//           return;
//       }
///////////////////////////////////////////////////////////////////////////

InsideIsInside(f',f,m);
InsideIsInside(t',t,m);

assert strictlyInside(f',m.o);
assert strictlyInside(t',m.o);

assert strictlyInside(f ,m.c);
assert strictlyInside(t ,m.c);



//       assert m.CalidLineKV(t',t);
//       assert mappingOwnersThruKlownKV(t', t, m);
//       assert mappingOWNRsThruKlownKV(t'.bound, t.bound, m);
//       assert mappingOWNRsThruKlownKV(t'.owner, t.owner, m);
//
//       assert mappingOWNRsThruKlownKV(f'.bound, f.bound, m);
//       assert mappingOWNRsThruKlownKV(f'.owner, f.owner, m);
//
//       assert strictlyInside(t', m.o);
//       assert f'.AMFO == t'.AMFX;




    // // assert SupaLine(t',t,m);
    // assert flatten(t'.owner) >= m.o.AMFO by { assert strictlyInside(t', m.o);       }
    // assert t.owner == (mapThruKlon(t'.owner - m.o.AMFO, m) + m.m[m.o].AMFO);
    // //assert t.owner == shiftAMFOZ(t'.owner, m.o.AMFO, m.m[m.o].AMFO, m.m);
    //       assert f  in t .owner;  //AMDI_FINT //GREENLAND
    //       assert f.AMFO == t.AMFX;
      assert refDI(f,t);
      return;
     }

assert false;
  }
