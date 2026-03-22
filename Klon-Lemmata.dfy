include "Klon.dfy"


///////// basic

lemma MapThruKlonIsVMap(kk: set<Object>, m : Klon, vv : set<Object>)
  requires kk <= m.m.Keys
  requires mapThruKlon(kk, m) == vv
   ensures mapThruVMap(kk, m.m) == vv
   {}

lemma {:isolate_assertions} HNSV(v : Object, m : Klon)
  ensures v in m.hns({v})
  {}




/////// (con)versions?


lemma {:isolate_assertions} OwnersFromCalid(m : Klon)
  requires m.SuperCalidFragilistic()
   ensures m.SuperCalidOwners()
   ensures m.CalidOwners()
{
    assert m.preOwners();
    assert m.preOwners2();
    assert (m.m.Keys <= m.oHeap);
    assert m.objectInKlown(m.o);
    assert m.AllLinesCalid();
    assert (forall k <- m.m.Keys :: m.OwnersLineKV(k, m.m[k]));
}


lemma {:isolate_assertions} {:timeLimit 40} CalidFromOwners(m : Klon)
  requires m.CalidOwners()
  requires m.HeapContextReady()
  requires m.ValuesContextReady()
   ensures m.SuperCalidFragilistic()
{
    assert (forall k <- m.m.Keys :: m.OwnersLineKV(k, m.m[k]));
    assert m.preOwners();
    assert m.preOwners2();
    assert (m.m.Keys <= m.oHeap);
    assert m.objectInKlown(m.o);
    assert forall k <- m.m.Keys :: (k.AMFX <= m.m.Keys) && (k.AMFB <= m.m.Keys);

//                assert forall k <- m.m.Keys :: (

  forall k <- m.m.Keys ensures (m.CalidLineKV(k,m.m[k]))
    //by
            {
                      //body of CalidLIneKV as of 25 Jan 2026
                      var v := m.m[k];
 assert               && (k in m.oHeap)
                      && (not(inside(k,m.o)) ==> (v == k))
                      && (   (inside(k,m.o)) ==> (v !in m.oHeap))
                  //    && (   (inside(k,o)) ==> (v.AMFO  >= v.AMFB >= k.AMFB))  //Beady2() GREENLAND
                      && (   (inside(k,m.o)) ==> (k.AMFB <= m.o.AMFB) )  // GREENLAND Beady2()  GREENLAND -
                      && (k.AMFX <= m.m.Keys)
                      && (k.AMFB <= m.m.Keys)
                      && (m.ownersInKlown(k))  //belt and braces--- currently a requirement!
                      && (checkOwnershipOfClone(k,v, m))
                      && (checkBoundOfClone(k,v, m))
                      && (mappingOwnersThruKlownKV(k,v, m))
                   ;
    assert m.AllLinesCalid();
     }
}

lemma {:isolate_assertions} OwnersLineFromCalidLine(k : Object, v : Object, m : Klon)
    requires m.apoCalidse()
    requires k.Ready()// && k.Valid() // should context go in here too? probasbly?
    requires m.ownersInKlown(k)
    requires v.Ready()
    requires v in m.hns({v})
    requires m.CalidLineKV(k,v)
     ensures m.OwnersLineKV(k,v)
    {}

//// mappings

lemma MapThruKlonFrom(os: set<Object>, m : Klon, m' : Klon)
  requires os <= m'.m.Keys
  requires m.from(m')
  ensures  mapThruKlon(os, m) == mapThruKlon(os, m')
{}

lemma MapThruKlonFUCKED(os: set<Object>, ot : set<Object>,  m : Klon)
  requires os <= m.m.Keys
  requires ot <= m.m.Keys
  requires os == ot
  ensures  mapThruKlon(os, m) == mapThruKlon(ot, m)
{}

lemma MapThruKlonLEQ(os: set<Object>, ot : set<Object>,  m : Klon)
  requires os <= m.m.Keys
  requires ot <= m.m.Keys
  requires os <= ot
  ensures  mapThruKlon(os, m) <= mapThruKlon(ot, m)
{}


lemma MapThruKlonGEQ(os: set<Object>, ot : set<Object>,  m : Klon)
  requires os <= m.m.Keys
  requires ot <= m.m.Keys
  requires os >= ot
  ensures  mapThruKlon(os, m) >= mapThruKlon(ot, m)
{}


lemma MapThruKlonID(os: set<Object>, m : Klon)
  requires os <= m.m.Keys
  requires forall x <- os :: m.m[x] == x
  ensures  mapThruKlon(os, m) == os
{}


lemma MapThruKlonIsMapThruVMap(ks: set<Object>, m : Klon, vs : set<Object>)
  requires ks <= m.m.Keys
  requires mapThruKlon(ks, m)   == vs
  ensures  mapThruVMap(ks, m.m) == vs
{}



lemma ThereAndKlonAgain1(os: set<Object>, m : Klon, r : set<Object>)
  requires os <= m.m.Keys
  requires r  == mapThruKlon(os,m)
   ensures r  <= m.m.Values
   ensures os == mapBackKlon(r,m)
{
  InversionLove(m.m, invert(m.m));
  assert r  == mapThruKlon(os,m);
  assert os == mapBackKlon(r,m);
}

lemma ThereAndKlonAgain2(os: set<Object>, m : Klon, r : set<Object>)
  requires os <= m.m.Values
  requires r == mapBackKlon(os,m)
   ensures r  <= m.m.Keys
   ensures os  == mapThruKlon(r,m)
 {
    InversionLove(m.m, invert(m.m));
 }




//SuperDuperMappers --- well on the way but could do with a bnit more qwork

lemma {:isolate_assertions} SuperDuperExternalMapperKV(k : Object, v : Object, m : Klon)
  //outside stuff is maping. (and equa;)
    requires m.apoCalidse()
    requires m.ownersReadyInKlown(k)
    requires m.SuperCalidFragilistic()
    requires v.owner == computeOwnerForClone(k.owner, m)
    requires v.bound == computeOwnerForClone(k.bound, m)
    requires outside(k, m.o)
     ensures mappingOWNRsThruKlownKV(k.owner,v.owner,m)
     ensures mappingOWNRsThruKlownKV(k.bound,v.bound,m)
{}


lemma {:isolate_assertions} SuperDuperPivotMapperKV(k : Object, v : Object, m : Klon)
  //consistency lemma… or somesthing.
    requires m.apoCalidse()
    requires m.ownersReadyInKlown(k)
    requires m.SuperCalidFragilistic()
    requires v.owner == computeOwnerForClone(k.owner, m)
    requires v.bound == computeOwnerForClone(k.bound, m)
    requires k == m.o
     ensures mappingOWNRsThruKlownKV(k.owner,v.owner,m)
     ensures mappingOWNRsThruKlownKV(k.bound,v.bound,m)
{}


lemma {:isolate_assertions} SuperDuperKlonMapperKV(m : Klon)
  //consistency lemma… or somesthing.kkkkk
    requires m.apoCalidse()
    requires m.ownersReadyInKlown(m.o)
    requires m.SuperCalidFragilistic()
// i  ensures mappingOWNRsThruKlownKV(m.o.owner,m.m[m.o].owner,m)
//     ensures mappingOWNRsThruKlownKV(m.o.bound,m.m[m.o].bound,m)
     ensures m.m[m.o].owner == m.clowner
     ensures m.m[m.o].bound == m.clbound
{}



lemma {:isolate_assertions} SuperDuperOwnerMapperKV(k : Object, v : Object, m : Klon)
  //consistency lemma… or somesthing.
    requires m.apoCalidse()
    requires m.ownersReadyInKlown(k)
    requires m.SuperCalidFragilistic()
    requires k.Ready()
    requires v.Ready()
    requires m.CalidLineKV(k,v)
    requires m.OwnersLineKV(k,v)
//  requires v.owner == computeOwnerForClone(k.owner, m)
//  requires v.bound == computeOwnerForClone(k.bound, m)
     ensures mappingOwnersThruKlownKV(k,v,m)
     ensures (k == m.o) ==> (
          && (v == m.m[m.o])
          && (v.owner == m.clowner)
          && (v.bound == m.clbound))
     ensures (outside(k, m.o)) ==> (v == k)
     ensures (strictlyInside(k, m.o)) ==> (
          && mappingOWNRsThruKlownKV(k.owner,v.owner,m)
          && mappingOWNRsThruKlownKV(k.bound,v.bound,m)
          && v.owner == computeOwnerForClone(k.owner, m)
          && v.bound == computeOwnerForClone(k.bound, m)
         )
{}


lemma {:isolate_assertions}  MappingInsideOwnersThruKlown(k : Object, v : Object, m : Klon)
   decreases k.AMFO
    requires k.Ready()
    requires v.Ready()
    requires m.apoCalidse()
    requires m.ownersReadyInKlown(k)
    requires strictlyInside(k, m.o)
    requires k in m.m.Keys
    requires m.m[k] == v

      ensures strictlyInside(v, m.m[m.o])

      requires mappingOwnersThruKlownKV(k,v,m)
      requires mappingOWNRsThruKlownKV(k.owner, v.owner, m)
      ensures forall oo <- k.owner | strictlyInside(oo,m.o) :: m.m[oo] in v.owner
      ensures inside(v, m.m[m.o])
  {
    assert v.owner == (set x <- (k.owner - m.o.AMFO) :: m.m[x]) + m.m[m.o].AMFO;
  }







lemma {:isolate_assertions} MappedBounds(k : Object, v : Object, m : Klon)
    requires k.Ready()
    requires v.Ready()
    requires m.ownersInKlown(k)
    requires m.SuperCalidFragilistic()

    requires strictlyInside(k, m.o)
     ensures k.AMFO > m.o.AMFO

    // ensures (forall oo <- k.AMFX :: k.AMFB <= oo.AMFB)  //GREENLAND //Beady2()
    ensures nuBoundsOK(k.owner, k.bound)

    requires mappingOWNRsThruKlownKV(k.owner, v.owner, m)
   //  ensures (forall oo <- v.AMFX :: v.AMFB <= oo.AMFB)  //GREENLAND //Beady2()
       ensures nuBoundsOK(v.owner, v.bound)
  {
    k.ExtraReady();  //GREENLAND //Beady2()
    v.ExtraReady();  //GREENLAND //Beady2()
    assert nuBoundsOK(k.owner, k.bound);
    assert nuBoundsOK(v.owner, v.bound);
//    assert (forall oo <- k.AMFX :: k.AMFB <= oo.AMFB + k.owner);   //GREENLAND //Beady2()
//    assert (forall oo <- v.AMFX :: v.AMFB <= oo.AMFB + v.owner);  //GREENLAND //Beady2()

    assert  k.AMFX >= k.AMFB;
    assert  (forall oo <- k.AMFX :: oo in m.m.Keys);
    assert  m.HeapContextReady();
    assert  m.ValuesContextReady();
    assert  AllReady(m.hns());

    var nuowner := computeOwnerForClone(k.owner,m);
    assert nuowner <= m.hns();
    assert  AllReady(nuowner);
    assert  AllReady(flatten(nuowner));
    var nubound := computeOwnerForClone(k.bound,m);
    assert nubound <= m.hns();
    assert  AllReady(nubound);
    assert  AllReady(flatten(nubound));
    var fvbound := flatten(nubound);
    var fvowner := flatten(nuowner);

    assert nuowner == global(sideways(local(k.owner, m),m),m);
    assert nubound == global(sideways(local(k.bound, m),m),m);



    //  assert fvowner >= fvbound;                                  //THULE  //TODO
    //  assert (forall vo <- fvowner :: fvbound <= vo.AMFB);        //THULE  //TODO

//    assert fvbound >= collectBounds(fvowner);  //TODO NUBIOUBNDS...
  }


lemma {:isolate_assertions}  MappingSameObjectIsOutsideThruKlown(k : Object, v : Object, m : Klon)
//wrong turn on the rocky road to dublin…
//answer - it works cos saying  m.m[k] == k == v
// constraints the spec so there are no solutions - except outside?
   decreases k.AMFO
    requires k.Ready()
    requires v.Ready()
    requires m.SuperCalidFragilistic()
    requires m.objectReadyInKlown(k)
    requires m.m[k] == k == v

    ensures outside(k, m.o)
{
   assert m.AllLinesCalid();
   assert m.CalidLineKV(k,v);
   assert mappingOwnersThruKlownKV(k, v, m);
}

lemma {:isolate_assertions}  MappingInsideBoundsThruKlown(k : Object, v : Object, m : Klon)
//wrong turn on the rocky road to dublin…
//answer - it works cos saying "outside" overconstraints the spec so there are no solutions
//saying m.m[k] == v gives us outside
   decreases k.AMFO
    requires k.Ready()
    requires v.Ready()
    requires m.apoCalidse()
    requires m.ownersReadyInKlown(k)
    // requires strictlyInside(k, m.o)  //how the hell does it work without this?

    //requires outside(k, m.o)

    requires k in m.m.Keys
    requires m.m[k] == v

    ensures flatten(k.owner) >= flatten(k.bound)
    ensures flatten(v.owner) >= flatten(v.bound)

    ensures strictlyInside(v, m.m[m.o])

    requires mappingOwnersThruKlownKV(k,v,m)
    requires mappingOWNRsThruKlownKV(k.bound, v.bound, m)
    requires mappingOWNRsThruKlownKV(k.owner, v.owner, m)

    ensures forall oo <- k.owner | strictlyInside(oo,m.o) :: m.m[oo] in v.owner
    ensures inside(v, m.m[m.o])
  {
    assert v.owner == (set x <- (k.owner - m.o.AMFO) :: m.m[x]) + m.m[m.o].AMFO;
}






//// less basic



lemma {:isolate_assertions} OwnershipOfCloneGEQ(os: set<Object>, ot : set<Object>,  m : Klon)
//
///kj 7 June 2025 - not claer how this  works if we're comaring owners and bounds?
  requires os <= m.m.Keys <= m.oHeap
  requires ot <= m.m.Keys <= m.oHeap
  requires os >= ot

  requires m.apoCalidse()
  requires m.SuperCalidFragilistic()

  requires m.m.Values <= m.hns()
  requires m.o.Ready()
  requires m.objectInKlown(m.o)
  requires m.HeapOwnersReady()
  requires m.c_amfx <= m.oHeap  //flattened ownershio of the top of the clone... - 'tis OK cos its the very top
   ensures computeOwnerForClone(os, m) >= computeOwnerForClone(ot, m)
{}





lemma {:isolate_assertions} OwnershipOfCloneGEQ2(os: set<Object>, ot : set<Object>, m : Klon, ro : set<Object>, rt : set<Object>)
  requires os <= m.m.Keys <= m.oHeap
  requires ot <= m.m.Keys <= m.oHeap
  requires os >= ot

  requires m.apoCalidse()
  requires m.SuperCalidFragilistic()

  requires m.m.Values <= m.hns()
  requires m.o.Ready()
  requires m.objectInKlown(m.o)
  requires m.HeapOwnersReady()
  requires m.c_amfx <= m.oHeap  //flattened ownershio of the top of the clone... - 'tis OK cos its the very top

   requires ro == computeOwnerForClone(os, m)
   requires rt == computeOwnerForClone(ot, m)

   ensures computeOwnerForClone(os, m) >= computeOwnerForClone(ot, m)
{}








//timelimit 60 BUT IT WORDS - 2 Jan 2026
//but it doesn't 5 Mar 2026
//we don't need this so switched off -
lemma {:isolate_assertions} {:verify false} BROKENCalidKVCalid(k : Object, v : Object, m0 : Klon, m1 : Klon)
  //if m0.klonKLV(kv == m1,  and m0 is calid, can m1 pretty please be calid()?
    requires m0.CKV_preconditions(k,v)
    requires m0.apoCalidse()
    requires k.Ready()// && k.Valid() // should context go in here too? probasbly?
    requires m0.ownersInKlown(k)
    requires v.Ready()
    requires m0.Calid()
    requires m0.CalidLineKV(k,v)
    requires k !in m0.m.Keys
    requires v !in m0.m.Values
    requires v in  m0.hns({v})
    requires m1.from(m0)
    requires m1 == klonKV(m0,k,v)
     ensures m1.m == vmapKV(m0.m,k,v)
     ensures k in m1.m.Keys
     ensures m1.m.Keys   == m0.m.Keys + {k}
     ensures m1.m.Values == m0.m.Values + {v}
     ensures m1.m[k] == v
     ensures m1.objectInKlown(k)
     ensures m1.Calid() //ERR
    {
      assert m0.AllLinesCalid();
      assert m0.CalidLineKV(k,v);
        assert m0.gettingThere();
      assert && (k.Ready())
               && (m0.ownersInKlown(k))
               && (v.Ready())
               && (v in m0.hns({v}));

      assert (k.Ready());
      assert (m1.ownersInKlown(k));
      assert (v.Ready());
      assert (v in m1.hns({v}));

      assert k in m1.m.Keys;
      assert m1.objectInKlown(k);

      assert m1.m.Keys == m0.m.Keys + {k};

      forall j <- m1.m.Keys ensures (
                              && (j.Ready())
                              && (m1.objectInKlown(j))
                              && (m1.m[j].Ready())
                              && (m1.m[j] in m1.hns())
                              && (m1.CalidLineKV(j,m1.m[j]))
                                   )
        {
         if (j == k)
           { assert m0.CalidLineKV(j,v);
             m0.CalidLineKVTo(j,v,m1);
             assert m1.CalidLineKV(j,v);
             assert m1.m[j] == v;
             assert m1.CalidLineKV(j,m1.m[j]);
           } else {
             assert j in m0.m.Keys;
             assert m0.m[j] == m1.m[j];
             assert m0.AllLinesCalid();
             assert m0.CalidLineKV(j,m0.m[j]);
             m0.CalidLineKVTo(j,m1.m[j],m1);
             assert m1.CalidLineKV(j,m1.m[j]);
           }
        }

        assert m1.gettingThere();

        assert m0.ValuesContextReady();
        assert m1.m.Values == m0.m.Values + {v};
        assert m1.hns() == m0.hns({v});
          assert v.Context(m0.hns({v}));
        assert v.Context(m1.hns());
//      assert forall x <- m0.m.Values :: x.Context(m0.hns()) && x.Context(m1.hns());
        forall  x <- m0.m.Values ensures (x.Context(m1.hns())) //by
          {
            assert x.Context(m0.hns());
            x.WiderContext(m0.hns(), m1.hns());
            assert x.Context(m1.hns());
          }
        assert forall x <- m1.m.Values ::
           if (x in m0.m.Values)
              then (x.Context(m1.hns()))
              else ((x == v) && (x.Context(m1.hns())));
        assert m1.ValuesContextReady();
  }



lemma {:isolate_assertions} {:timeLimit 0} BETTERCalidKVCalid(k : Object, v : Object, m0 : Klon, m1 : Klon)
  //if m0.klonKLV(kv == m1,  and m0 is calid, can m1 pretty please be calid()?
    requires m0.CKV_preconditions(k,v)
//requires HighCalidFragilistic(m0)
    requires m0.apoCalidse()
    requires k.Ready()// && k.Valid() // should context go in here too? probasbly?
    requires m0.ownersInKlown(k)
    requires v.Ready()
    requires m0.Calid()
    requires m0.CalidLineKV(k,v)
    requires k !in m0.m.Keys
    requires v !in m0.m.Values
    requires v in  m0.hns({v})
    requires m1.from(m0)
    requires m1 == klonKV(m0,k,v)
     ensures m1.m == vmapKV(m0.m,k,v)
     ensures k in m1.m.Keys
     ensures m1.m.Keys   == m0.m.Keys + {k}
     ensures m1.m.Values == m0.m.Values + {v}
     ensures m1.m[k] == v
     ensures m1.objectInKlown(k)
     ensures m1.Calid()
//ensures HighCalidFragilistic(m1)

{
    assert m1 == m0.CalidKV(k,v);
    assert m1.Calid();
    //assume m1.Calid();  //still crashes
}





//this costs 0.08ms - who knows whw?
lemma OIKsisOIKs(o : Object, m : Klon)
  requires o.Ready()
  requires m.ownersInKlown(o)
  ensures forall oo <- o.AMFO | oo != o :: m.ownersInKlown(oo)
  ensures forall oo <- o.AMFX :: m.ownersInKlown(oo)
{}


////////// shifting


function {:isolate_assertions} shiftObject(i0 : Object, m : Klon) : (i1 : Object)
// see below BETTER version but with stronger preconditions
// kept this one becuase the necessary refactoring needs to come later //JDl
    requires m.apoCalidse()
//    requires m.SuperCalidFragilistic()
//     ensures m.AllLinesCalid()
    requires i0.Ready()
    requires inside(i0, m.o)
    requires m.objectInKlown(i0)

//    ensures inside(i1, m.m[m.o] )
    //    reads m.hns()
    { m.m[i0] }





function {:isolate_assertions} shiftAMFO(i0 : OWNR, x0 : OWNR, x1 : OWNR, im : vmap<Object, Object>) : (i1 : OWNR)
 //given i0 insidfe x0, shift it sideways to the same relationship with w1
 //fuck - perhaps this needs a Klon.  probalby does!
 // lemmee guess, this thrns out to b som version of nmapwthKlon.  fucker.  commie FUCK.
 // except coming in as OWNRs not Owners or Objects
 //grrr
 //**wont verify with just apoCalidse..  */
  requires i0 >= x0
  requires i0 <= im.Keys
     //aka requires im.Keys >= i0 >= x0
   ensures i1 >= x1
   ensures i1 == (set o <- (i0 - x0) :: im[o]) + x1
               { (set o <- (i0 - x0) :: im[o]) + x1 }

function {:isolate_assertions} shiftAMFOF(i0 : OWNR, x0 : OWNR, x1 : OWNR, im : vmap<Object, Object>) : (i1 : OWNR)
 //given i0 insidfe x0, shift it sideways to the same relationship with w1
 //fuck - perhaps this needs a Klon.  probalby does!
 // lemmee guess, this thrns out to b som version of nmapwthKlon.  fucker.  commie FUCK.
 // except coming in as OWNRs not Owners or Objects
 //grrr
 //**wont verify with just apoCalidse..  */
  requires flatten(i0) >= x0
  requires i0 <= im.Keys
     //aka requires im.Keys >= i0 >= x0
   ensures flatten(i1) >= x1
   ensures i1 == (set o <- (i0 - x0) :: im[o]) + x1
               { (set o <- (i0 - x0) :: im[o]) + x1 }



function {:isolate_assertions} shiftAMFOZ(i0 : OWNR, x0 : OWNR, x1 : OWNR, im : vmap<Object, Object>) : (i1 : OWNR)
 //given i0 insidfe x0, shift it sideways to the same relationship with w1
 //fuck - perhaps this needs a Klon.  probalby does!
 // lemmee guess, this thrns out to b som version of nmapwthKlon.  fucker.  commie FUCK.
 // except coming in as OWNRs not Owners or Objects
 //grrr
 //**wont verify with just apoCalidse..  */
  requires i0 <= im.Keys
     //aka requires im.Keys >= i0 >= x0
   ensures i1 == (set o <- (i0 - x0) :: im[o]) + x1
               { (set o <- (i0 - x0) :: im[o]) + x1 }








lemma {:isolate_assertions} SubObjectsGeqViaOWNRs(p0 : Object, w0 : Object, p1 : Object, w1 : Object, m : Klon)
    requires m.SuperCalidFragilistic()
    requires m.objectReadyInKlown(p0)
    requires m.objectReadyInKlown(w0)
    requires inside3(p0,w0,m.o)
    requires not(inside(w1, w0)) // careful because we want !>= relation, as against < or <=
    requires p1.AMFO == shiftAMFO(p0.AMFO, m.o.AMFO, m.m[m.o].AMFO, m.m)
    requires w1.AMFO == shiftAMFO(w0.AMFO, m.o.AMFO, m.m[m.o].AMFO, m.m)
     ensures inside3(p1,w1,m.m[m.o])
{}


lemma {:isolate_assertions} SubAMFOsGeq(p0 : OWNR, w0 : OWNR, p1 : OWNR, w1 : OWNR, m : Klon)
    //p0 and w0 are flattened owners )AMFOs( within pivot x0;  (original)
    //p1 and w1 are flattened owners )AMFOs( within copivot x1;  (clone)
    requires m.SuperCalidFragilistic()
    requires m.m.Keys >= p0 >= w0 >= m.o.AMFO
  //  requires not( w1 >= w0 ) // careful because we want !>= relation, as against < or <=
    requires p1 == shiftAMFO(p0, m.o.AMFO, m.m[m.o].AMFO, m.m)
    requires w1 == shiftAMFO(w0, m.o.AMFO, m.m[m.o].AMFO, m.m)

     ensures m.objectReadyInKlown(m.o)
     ensures m.m[m.o] in m.m.Values
     ensures sub(p0,m.o.AMFO) >= sub(w0,m.o.AMFO)
     ensures sub(p1,m.m[m.o].AMFO) >= sub(w1,m.m[m.o].AMFO)
     ensures p1 >= w1 >= m.m[m.o].AMFO
{
    assert m.SuperCalidFragilistic();
    assert m.objectReadyInKlown(m.o);
    assert m.m.Keys >= m.o.AMFO;
    assert forall oo <- m.o.owner :: (oo in m.m.Keys) && (m.m[oo] in m.m.Values);
    assert forall oo <- m.o.AMFO :: m.m[oo] in m.m.Values;

    assert m.OwnersLineKV(m.o, m.m[m.o]);
    assert mappingOwnersThruKlownKV(m.o, m.m[m.o], m);

    assert m.o.Ready();
    assert forall oo <- m.o.owner :: inside(m.o, oo);
    assert m.m[m.o].Ready();
    assert forall oo <- m.m[m.o].owner :: inside(m.m[m.o], oo);
}

lemma {:isolate_assertions} {:timeLimit 60} IWannaBeFoolish(i0 : Object, m : Klon, i1 : Object)
 //shiftObject is shiftAMFO is mappingOwnersThruKlownKV
  requires m.objectReadyInKlown(i0)
  requires m.SuperCalidFragilistic()
  requires inside(i0, m.o)
  requires m.m[i0] == i1 ///'not strong enough  (6 Oct 2025)
  requires i1.AMFO == shiftAMFO(i0.AMFO, m.o.AMFO, m.m[m.o].AMFO, m.m)
  requires forall z <- (m.m.Keys)   :: z.Ready()
  requires forall z <- (m.m.Values) :: z.Ready()
  requires forall z <- (i0.AMFO)    :: z.Ready()
  requires forall z <- (i1.AMFO)    :: z.Ready()
  requires flatten(i0.AMFO) <= m.oHeap
  requires flatten(i1.AMFO) <= m.hns(i1.AMFO)

   ensures i1 == shiftObject(i0, m)
   ensures i1.AMFO == shiftAMFO(i0.AMFO, m.o.AMFO, m.m[m.o].AMFO, m.m)
   ensures mappingOWNRsThruKlownKV(i0.AMFO, i1.AMFO, m)
   {

   var kk := i0.AMFO;
   var vv := (mapThruKlon(kk - m.o.AMFO, m) + m.m[m.o].AMFO);
   assert vv == i1.AMFO;

var si0 := i0.AMFO;
var sx0 := m.o.AMFO;
var sx1 := m.m[m.o].AMFO;
var slm := m.m;
var si1 := shiftAMFO(i0.AMFO, m.o.AMFO, m.m[m.o].AMFO, m.m);
assert si1 == (set o <- (si0 - sx0) :: slm[o]) + sx1;
assert si1 == (set o <- (i0.AMFO - m.o.AMFO) :: m.m[o]) + m.m[m.o].AMFO;
assert si1 == vv;

assert i1.AMFO == si1;

   }




lemma {:isolate_assertions} ShiftAMFOshiftOWNRs(kk : OWNR, vv : OWNR, m : Klon)
   //establishes that shiftAMFO(Kk) makes a vv that passes mappignOWNRS...
      requires m.apoCalidse()
      requires AllReady(kk)
      requires AllReady(vv)
      requires kk <= m.m.Keys
      requires kk >= m.o.AMFO

      requires flatten(kk) <= m.oHeap
      requires flatten(vv) <= m.hns(vv)  //kind of trivially true though...

      requires vv == shiftAMFO(kk, m.o.AMFO, m.m[m.o].AMFO, m.m)

       //ensures vv == (mapThruKlon(kk - m.o.AMFO, m) + m.m[m.o].AMFO)

       ensures mappingOWNRsThruKlownKV(kk, shiftAMFO(kk, m.o.AMFO, m.m[m.o].AMFO, m.m), m)
      {}


lemma {:isolate_assertions} ShiftOWNRshiftAMFOs(kk : OWNR, vv : OWNR, m : Klon)
    //or this? 0 if mappign OWNRS are OK< then shitAMFO doea the righ tthing
      requires m.apoCalidse()
      requires AllReady(kk)
      requires AllReady(vv)
      requires kk <= m.m.Keys

      requires kk >= m.o.AMFO
      requires mappingOWNRsThruKlownKV(kk, vv, m)
      ensures vv == shiftAMFO(kk, m.o.AMFO, m.m[m.o].AMFO, m.m)
      {}







function {:isolate_assertions} shiftObjectBETTER(i0 : Object, m : Klon) : (i1 : Object)
    requires m.apoCalidse()
    requires m.SuperCalidFragilistic()
     ensures m.AllLinesCalid()
     //needs HighLine stuff there to work!
//    requires HighCalidFragilistic(m)
  //     ensures HighLineKV(i0,i1,m)
    requires i0.Ready()
    requires inside(i0, m.o)
    requires m.objectInKlown(i0)
     ensures inside(i1, m.m[m.o])
       reads m.hns()
    { m.m[i0] }





lemma {:isolate_assertions} {:resource_limit 0} {:verify false}  INSIDEOUT(oo : OWNR, m : Klon)   ///it'll be somethign missing that's in HighLine but not other lines
   requires forall o <- oo :: m.objectReadyInKlown(o)
   requires oo <= m.m.Keys
   // requires HighCalidFragilistic(m)
        requires m.SuperCalidFragilistic()
    ensures ((set o <- oo | inside(o, m.o)) == {})  ==> (forall o <- oo :: outside(o, m.o))
    ensures ((set o <- oo | inside(o, m.o)) == {}) <==  (forall o <- oo :: outside(o, m.o))

    ensures ((set o <- oo | inside(o, m.o)) >  {})  ==> (exists o <- oo :: inside(o, m.o))
    ensures ((set o <- oo | inside(o, m.o)) >  {}) <==  (exists o <- oo :: inside(o, m.o))

    ensures ((set o <- oo | inside(o, m.o)) >  {})  ==> (not (forall o <- oo :: outside(o, m.o)))
    ensures ((set o <- oo | inside(o, m.o)) >  {}) <==  (not (forall o <- oo :: outside(o, m.o)))
 {}
