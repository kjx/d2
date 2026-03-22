include "Ownership.dfy"


// //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
// //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
// //
// //  Klon - clone mapping!
// //
// //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
// //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//
//
//
//  thinkgs to add - the two level version?  (PreKlon and Klon?)
//    c - : objecet --=- the top of the clone! hurrah! m.m[m.o]!

datatype Klon = Klon
(
  m : vmap<Object,Object>,    //the  klon map
  o : Object,                 //object being copied
  clowner : Owner,            //owner of the clone
  clbound : Owner,            //bound of the clone
  oHeap : set<Object>,        //heap
  o_amfx : Owner,             //was o. so the AMFX of o
  //  c_amfb : OWNR,              //epected flattened bound of the clone..
  c_amfx : Owner              //epected flattened ownershio of the clone..
)
{
  function  ns(os : set<Object> := {}) : set<Object> { m.Values+os        }
  function hns(os : set<Object> := {}) : set<Object> { oHeap+m.Values+os  }

  predicate from(prev : Klon) : (r : bool)
    ensures r ==> (isFlat(prev.oHeap) ==> isFlat(oHeap))
  {
    && mapGEQ(m,  prev.m)
    && o       == prev.o
    && clowner == prev.clowner
    && clbound == prev.clbound
    && oHeap   == prev.oHeap     //OPTION - considere incorporating ApoCalidseNow...
    && o_amfx  == prev.o_amfx
    && c_amfx  == prev.c_amfx
       //option ie allow heaps to get bigger, so long as all keys are in the heap
  }


  predicate HeapOwnersReady()
    reads {}
  { forall x <- oHeap :: (x.AMFO <= oHeap) }

  predicate ValuesOwnersReady()
    reads {}
  {
   forall x <- m.Values :: (x.AMFO <= hns())
  }

  predicate HeapContextReady()
    reads oHeap
  {///prog 1 Augu 2025 - not sure this is right cos
   ///do3esentt that contradict the heap p      ointoting to na
   ///i.e. heap ispart of hns isn't it?
   ///answer yes, but that doen't happen during a clone() operation...
    (forall x <- oHeap :: (x.Ready() && x.Valid() && x.Context(oHeap)))
  }

  predicate ValuesContextReady()
    reads m.Values, oHeap
  {
    //prog experimental!! 11 aug 2025
   forall x <- m.Values :: x.Context(hns())  ///prog HACKED 4 Oct 2025    ///shojld this say "READY"
  //or should this be hns too?
//    (forall x <- m.Values :: (x.Ready() && x.Valid() && x.Context(hns())))
  }

predicate ValueInContext(v : Object)
  requires ValuesContextReady()   //WHAT THE FUYCK???
  requires v in hns()
  reads hns(),  m.Values, oHeap
  { (v.Ready() && v.Valid() && v.Context(hns())) }



  ghost predicate {:isolate_assertions}   preCalid() : (r : bool)
    //Klon mapping is consitent & valid.
    //Calid just seened like a good name
    reads oHeap, m.Values

    // requires HeapContextReady()
    // requires ValuesContextReady()
  {
    //internal consistency
    //note that the pivot object being clone "o"
    //does not hace to be in the map at the start.

    //&& (isFlat(oHeap))  //progFEARSATAN

    && HeapContextReady()
    && ValuesContextReady()

    && (o in oHeap)
    && (objectInKlown(o))  //progFUCK  do i want this in here? really?   ///Can U do without it??
    && (o.AMFX == o_amfx)
//WTF    && (flatten(clbound) >= o.AMFB)
    && (nuBoundsOK(o.owner, o.bound))
    && (o.AMFO == o_amfx+{o})
   //bound can only move DOWN
    //    && (not(c_amfx > o_amfx)) //HUMBERT HUMBERT
    // important to note that c_amfx can be any distance below o_amfx -
    // or more accurately, any distance below o.bound
    // which may (or may not) be *above*/*outside* o_amfx.
    && (c_amfx >= flatten(clbound) >= flatten(o.bound))
  }



  ghost predicate {:isolate_assertions} preCalid2() : (r : bool)
    //More PreCalid2 Stuff
    // reads oHeap`fields, oHeap`fieldModes
    // reads m.Keys`fields, m.Keys`fieldModes
    // reads m.Values`fields, m.Values`fieldModes
    // reads o`fields, o`fieldModes
    // reads m.Values, oHeap

    reads {}
  {
    //   m : vmap<Object,Object>,    //the  klon map
    //   o : Object,                 //object being copied
    //   clowner : Owner,            //owner of the clone
    //   clbound : Owner,            //bound of the clone
    //   oHeap : set<Object>,        //heap
    //   o_amfx : Owner,             //was o. so the AMFX of o
    // //  c_amfb : OWNR,              //epected flattened bound of the clone..
    //   c_amfx : Owner

    && (c_amfx <= oHeap) //should goto precalid1??
      //Llooks kinda odd...

    && ((o in m.Keys) ==> (
        var c := m[o]; //WE HAS KLONE
         ///&& add in c.Ready()???
          && (c_amfx  == c.AMFX)
          && (clowner == c.owner)
          && (clbound == c.bound)

          && (c  in m.Values)
          && (c !in oHeap)
       ))
  }

  ghost predicate {:isolate_assertions} SuperCalidFragilistic() : (r : bool)
    //Klon mapping is consitent & valid.
    //Calid just seened like a good name

    reads oHeap, m.Values
///can goto reads {} bia HeapOwnersReady && ValuesOwnersReady…

    // reads oHeap`fields, oHeap`fieldModes
    // reads m.Keys`fields, m.Keys`fieldModes
    // reads m.Values`fields, m.Values`fieldModes
    // reads o`fields, o`fieldModese
    // reads m.Values, oHeap
  {
//    false  //WHAT THE FUCKY FUCK FUCK???4
    && HeapContextReady()
    && ValuesContextReady()
    && Calid()
  }

  //opaque
  ghost predicate {:isolate_assertions} Calid() : (r : bool)
    //Klon mapping is consitent & valid.
    //Calid just seened like a good name

    //dont call this directly - call SuperCalid
    requires  HeapContextReady()
    requires  ValuesContextReady()

    reads oHeap, m.Values
 {
    //internal consistency
    && preCalid()
    && preCalid2()

    //calidObjects - mostly about oHeap and ns and stuff
    && (m.Keys <= oHeap)
    && (forall k <- m.Keys :: (k.Ready() && k.Valid()))   //note no Context

    //this recapitulates ValuesContextReady() but putting it here lets things work
    && (forall v <- m.Values :: (v.Ready() && v.Valid()))    //note no Context

    //the pivot object "o" being cloned
    // && (o.Ready() && o.Valid() && o.Context(oHeap) && objectInKlown(o))
    && (o.Ready() && o.Valid() && o.Context(oHeap) && objectInKlown(o))

    //what's all this SHIT and why is it here and how doe it realte to allLinesCallid etc!
    && (forall k <- m.Keys   :: m[k].AMFO  >= m[k].AMFB  >= k.AMFB)
//      && (forall k <- m.Keys   :: m[k].AMFO  >= m[k].AMFB >= o.AMFB >= k.AMFB)   ///change made then backed out 10Jul 2025 - why wo why oh why ?

    // && (forall k <- m.Keys   :: m[k].owner >= m[k].bound >= k.bound)
    && (forall k <- m.Keys   :: (not(inside(k,o)) ==> (m[k] == k)))
    && (forall k <- m.Keys   :: (   (inside(k,o)) ==> (m[k] !in oHeap)))
    //
    //calidSheep - su WRONGbsumed?
    //12 Jine 2025 clipping this out for now

    //KlonVMqpOK(k, context)
    && (forall k <- m.Keys :: k.AMFO <= m.Keys)
    && (forall k <- m.Keys :: k.AMFB <= m.Keys)

    && (&& (HeapOwnersReady())
        //  && ((forall x <- m.Keys :: x.Ready() && x.Valid() && x.Context(oHeap) && objectInKlown(x)   ))
        && (ValuesOwnersReady())
        && (gettingThere())
        && (AllLinesCalid()))

    //    && (forall k <- m.Keys :: ownersInKlown(k) && checkClownership(k, m[k], this))
  }



//   //removeing the var declaratioon on this end
//   //made things work on the other!
  predicate gettingThere() reads {} {
    // forall k <- m.Keys ::
    //     (var v := m[k];
    //     && (k.Ready())
    //     && (objectInKlown(k))
    //     && (v.Ready())
    //     && (v in hns({v})))
    forall k <- m.Keys :: (
                            && (k.Ready())
                            && (objectInKlown(k))
                            && (m[k].Ready())
                            && (m[k] in hns())
                          )

  }

//
//   //and again --- isses are things like HeapContexReady, ValuesContext, reqs vs conjuncts,
  predicate {:isolate_assertions} AllLinesCalid()
    //all pairs (aka lines) in the overall Klon map are Calid
    requires gettingThere()

    requires o.Ready() && objectInKlown(o)
    requires m.Keys <= oHeap

    //what's left of the six requirements of preCalid2 / computeOwnerForClone apocalypse
    requires HeapOwnersReady()
    requires c_amfx <= oHeap
    reads oHeap, m.Values
  {
    (forall k <- m.Keys :: CalidLineKV(k, m[k]))
  }

//
//
//
//
//

  lemma {:isolate_assertions} {:timeLimit 20} CalidLineKVTo(k : Object, v : Object, m1 : Klon)
    requires apoCalidse()
    requires k.Ready()// && k.Valid() // should context go in here too? probasbly?
    requires ownersInKlown(k)
    requires v.Ready()
    requires CalidLineKV(k,v)
    requires m1.from(this)
    requires m1.apoCalidse()
     ensures m1.CalidLineKV(k,v)
{}


  predicate {:isolate_assertions} CalidLineKV(k : Object, v : Object)
    //conditions for individual mappings (pairs aka lines) in the overall Klon map
    //this shoiuld work for lines *already* in the Klon
    //*as well as* for lines that aren't into the Klon
    ///(but it won't tell you if you can add them cos they could be already in there)
    requires apoCalidse()
    requires k.Ready()// && k.Valid() // should context go in here too? probasbly?
    requires ownersInKlown(k)
    requires v.Ready()

    reads oHeap, m.Values
  {

    && (k in oHeap)    //this one is easy - what to do for things like v.AMFO aren't...
    //or perhaps it is - they either ibn the preheap or ns newstuff
        //prog - 10 Aug 2025

    //the fundamental something-or-other
    && (not(inside(k,o)) ==> (v == k))
    && (   (inside(k,o)) ==> (v !in oHeap))
//    && (   (inside(k,o)) ==> (v.AMFO  >= v.AMFB >= k.AMFB))  //Beady2() GREENLAND
    && (   (inside(k,o)) ==> (k.AMFB <= o.AMFB) )  // GREENLAND
      ////Beady2()  GREENLAND -
  //    && (   (inside(k,o)) ==> (v.owner >= v.bound >= k.bound >= o.bound))

//    && ( (v.AMFO > v.AMFB  >= k.AMFB) )   //GREENLAND

//  && ( (v.owner >= v.bound >= k.bound) )

    && (k.AMFX <= m.Keys)
    && (k.AMFB <= m.Keys)
//    && (k.bound <= k.owner <= m.Keys)
    && (ownersInKlown(k))  //belt and braces--- currently a requirement!
    && (checkOwnershipOfClone(k,v,this))
    && (checkBoundOfClone(k,v,this))

  //MAPPING - progFEARSATAN
    && (mappingOwnersThruKlownKV(k,v,this))

///k.fieldModes == v.fieldModes  ///or shoudl otherwise be compatible

  }

lemma MOVIN_ON_MAP(os: Owner, left : vmap<Object,Object>, right : vmap<Object,Object>)
  requires left.Keys >= right.Keys >= os
  requires forall o <- right.Keys :: left[o] == right[o]
  ensures  (set o <- os :: left[o]) == (set o <- os :: right[o])
{}



  predicate objectInKlown(o : Object) : (rv : bool)
    //o and all its owners etc are the Klown m
    //(doesn't extend to fields)
    //BUT should incorproate ready!! like ObjectReadyInKlon - merge these in
    reads {}
    requires o.Ready()

    ensures rv ==> (o in m.Keys)
    ensures rv ==> (o.AMFB <= m.Keys)
    ensures rv ==> (o.AMFX <= m.Keys)
    ensures rv ==> (o.AMFO <= m.Keys)    //WEESA DONT WANTA REQUIRE this MASSA
    ensures rv ==> (o.bound <= m.Keys)
    ensures rv ==> (o.owner <= m.Keys)
    ensures rv ==> (o.self  <= m.Keys)    //WEESA DONT WANTA REQUIRE this MASSA
  { o.AMFO <= m.Keys }


  predicate ownersInKlown(o : Object) : (rv : bool)
    //o's owners but not o itself is in the Klon
    //(doesn't extend to fields)
    reads {}

    //critical that thes does *not* catch AMFO or self ...
    requires o.Ready()

    ensures rv ==> (o.AMFB <= m.Keys)
    ensures rv ==> (o.AMFX <= m.Keys)
    ensures rv ==> (o.bound <= m.Keys)
    ensures rv ==> (o.owner <= m.Keys)
  { o.AMFX <= m.Keys }

  predicate objectReadyInKlown(o : Object) : (rv : bool)
    //o and all its owners etc are the Klown m
    //(doesn't extend to fields)
    reads {}

    ensures rv ==> (o in m.Keys)
    ensures rv ==> (o.AMFB <= m.Keys)
    ensures rv ==> (o.AMFX <= m.Keys)
    ensures rv ==> (o.AMFO <= m.Keys)
    ensures rv ==> (o.bound <= m.Keys)
    ensures rv ==> (o.owner <= m.Keys)
    ensures rv ==> (o.self  <= m.Keys)

    ensures (o.Ready() && rv) ==> objectInKlown(o)
    ensures  o.Ready() ==> (rv == objectInKlown(o))

  {
    o.Ready() && (o.AMFO <= m.Keys)
   }

  predicate ownersReadyInKlown(o : Object) : (rv : bool)
    ensures rv ==> (o.AMFB <= m.Keys)
    ensures rv ==> (o.AMFX <= m.Keys)
    ensures rv ==> (o.bound <= m.Keys)
    ensures rv ==> (o.owner <= m.Keys)
    ensures rv ==> (o.Ready())

    ensures (o.Ready() && rv) ==> ownersInKlown(o)
    ensures  o.Ready() ==> (rv == ownersInKlown(o))

    reads {}
    {
      o.Ready() && (o.AMFX <= m.Keys)
    }

//29 Oct 2025
//I think the quesiton is whether clowner have tio be in values.
//and ... it doesn't!!!
  // lemma ObjectValuesInKlownToo(o : O bject)
  //   requires objectInKlown(o)
  //   requires CalidOwners()
  //    ensures m[o].AMFO <= m.Values
  //       {
  //           assert o.AMFO <= n.Keys; requires f.AMFO >= t.AMFX   ///classic O-as-D, f->t ==> f inside T.owner
  //           assert forall x <- o.AMFO :: CalidLineKV(x, m[x]);
  //       }


predicate  apoCalidse()
   //the six requirements of preCalid2 / computeOwnerForClone apocalypse
   reads {}
  {
    && (m.Keys <= oHeap)
    && (m.Values <= hns())
    && (objectReadyInKlown(o))   //this was originally two predicates
    && (HeapOwnersReady())  //whatt bno value owners ready??
    && (c_amfx <= oHeap)
  }




//{:timeLimit 60}
  function {:isolate_assertions} {:timeLimit 30} CalidKV(k : Object, v : Object) : (mK : Klon)
    //givne a Calid Klon, add in k:=v to the mapping and get a  Calid result.
    //the heart of the heart of the klon

    requires CKV_preconditions(k,v)
    requires CalidLineKV(k,v)    requires CLKV: CalidLineKV(k,v)

     ensures mK == klonKV(this, k, v)
     ensures mK.from(this)
     ensures mK.HeapContextReady()
     ensures mK.ValuesContextReady()
     ensures mK.m.Keys <= mK.oHeap
     // ensures  unchanged(oHeap`fieldModes)
     // ensures  unchanged(m.Values`fieldModes)
     ensures forall z <- m.Keys :: m[z].fieldModes == mK.m[z].fieldModes

     ensures mK.Calid()
     ensures mK.SuperCalidFragilistic()

     reads oHeap, m.Values, k, v
     reads m.Keys, m.Values
  {
       assert CKV_preconditions(k,v);
    // assert CKV_preconditions(k,v);
    //
    //----------------------------------------------------------------------
    //
    // assert SuperCalidFragilistic();
    // assert k.Ready();
    // assert ownersInKlown(k);
    // assert o.Ready();
    // assert objectInKlown(o);
    // assert CalidCanKey(k);
    // assert k !in m.Keys;
    // assert v !in m.Values;
    // assert HeapContextReady();
    // assert ValuesContextReady();
    // assert Calid();
    // assert k in oHeap;
    // assert (v.Ready() && v.Context(hns({v})));
    // assert this.m.Keys <= this.oHeap;
    // assert klonVMapOK(m);
    // assert klonCanKV(this, k, v);
    // assert CalidLineKV(k,v);
    //
    //
    //     requires SuperCalidFragilistic()
    //
    //     requires k.Ready() //&& k.Valid() // should context go in here too? probasbly?
    //     requires ownersInKlown(k)   //be nice to get rid of this...
    //     requires o.Ready() //&& o.Valid()
    //     requires objectInKlown(o)
    //
    //     requires CalidCanKey(k)
    //
    //     requires k !in m.Keys
    //     requires v !in m.Values
    //
    //     // requires HeapContextReady()
    //     // requires ValuesContextReady()
    //     // requires Calid()
    //
    //     requires k in oHeap
    //     requires (v.Ready() && v.Context(hns({v})))
    //
    //     requires this.m.Keys <= this.oHeap
    //
    //     requires klonVMapOK(m)
    //     requires klonCanKV(this, k, v)
    //
    //     requires CalidLineKV(k,v)
    //
    //----------------------------------------------------------------------
//
//
//     assert preCalid();
//     assert preCalid2();
//     assert && (c_amfx <= oHeap);
//
//     assert HeapContextReady();
//
//     assert forall x <- m.Keys :: (x.Ready() && objectInKlown(x))
//       by { assert SuperCalidFragilistic(); }        // SuperCalidGetsAllOwnersReadyInKlown();\\
//
//     assert ValuesContextReady();
//     assert AllLinesCalid();
//
//
//     //use kalidLineKV rather than checkOwnershipOfClone(k, m[k], this);
//     //assert forall k <- m.Keys :: checkOwnershipOfClone(k, m[k], this);
//
  (
     var mK := klonKV(this, k, v);
     assert mK.m[k] == v;

     assert mK.m.Keys            == m.Keys+{k};
     assert mKmVmVv: mK.m.Values == m.Values+{v};
     assert          mK.m.Values == m.Values+{v};
     assert mK.from(this);

     assert hns({v}) == mK.hns({});
     assert v.Context(hns({v})) by { assert CKV_preconditions(k,v); }
     assert v.Context(mK.hns({}));

     forall x <- mK.m.Keys ensures {:contradiction} (mK.m.Keys <= oHeap) //by
     {
       if (x == k) { assert {:contradiction} k in oHeap; }
       if (x != k) { assert {:contradiction} x in oHeap; }
       assert {:contradiction} x in oHeap;
     }

     forall y <- mK.m.Values ensures (y.Context(mK.hns())) //by
     {
       if (y == v) { assert v.Context(mK.hns()); }
       if (y != v) {
         assert  {:contradiction} y in m.Values;
         assert  {:contradiction} y.Context(hns());
                                  y.WiderContext(hns(), mK.hns());
         assert  {:contradiction} y.Context(mK.hns()); }

     }

    //  forall y <- mK.m.Values ensures (y.Ready() && y.Valid() ) //by
    //  {
    //    if (y == v) { assert (v.Ready() && v.Valid()); }
    //    if (y != v) {
    //      assert  {:contradiction} y in mK.m.Values;
    //      assert  {:contradiction}  (y.Ready() && y.Valid()); }
    //  }



     assert {:contradiction} mK.HeapContextReady();
     assert ValuesContextReady();

     assert  forall x <- m.Values :: x.OwnersWithin(hns());
         // assert  (forall x <- m.Values :: (x.Ready() && x.Valid() && x.Context(hns())));

     assert v in mK.m.Values;
    //  assert v.Context(hns({v})) by { assert CKV_preconditions(k,v); }
     assert v.Context(mK.hns({}));
     assert mK.m.Values == m.Values + {v};

     assert forall x  : Object <-    m.Values + {v} :: x.OwnersWithin(hns({v}));
     assert forall x  : Object <- mK.m.Values       :: x.OwnersWithin(mK.hns());
//     assert mK.ValuesContextReady();

//      assert objectInKlown(o);
//      assert mK.objectInKlown(o);
//
//      assert CalidCanKey(k); //pro you're like to want to walk.
//      // ^-- no idea what that comment means but…
//   //seems a but fyckiung late for this level of quibling now!
// //     assert forall k <- m.Keys :: CalidLineKV(k,v);
//
//      assert mK.m.Keys == m.Keys + {k};
//     //
//     //  assert forall k <- mK.m.Keys :: mK.objectInKlown(k);
//

     assert CKV_preconditions(k,v);
     assert AllLinesCalid();
     assert forall x <- m.Keys :: CalidLineKV(x,m[x]);
     assert CalidLineKV(k,v); //GNT by { reveal CLKV; }
     assert mK.m[k] == v;
     CalidLineKVTo(k,mK.m[k],mK);
     assert mK.CalidLineKV(k,v);
     assert mK.CalidLineKV(k,mK.m[k]);
//
//      forall x <- m.Keys ensures ( this.CalidLineKV(x,m[x]) && ( mK.CalidLineKV(x,m[x])))
// {
//        assert CalidLineKV(x,m[x]);
//         //CUL  CalidLineKVKV(mK,x,this);  //wasKVDFrom!!!!Q
//
//        // assert x in mK.m.Keys;
//        // assert mK.m[x] == m[x];
//        // assert checkOwnershipOfClone(k,v,this);
//        //      CheckOwnershipOfCloneFrom(k, v, mK, this);
//        //      computeOwnerForCloneFrom(k, mK, th is);
//        // CalidlineFrom(mK,x,this);
//        //      assert checkOwnershipOfClone(k,v,mK);
//        assert mK.CalidLineKV(x,m[x]);
//       //
//       //  assert KCLX: mK.CalidLineKV(x,m[x]);
//       //  assert       mK.CalidLineKV(x,m[x]) by { reveal KCLX; }
//       //  assert (this.CalidLineKV(x,m[x]) && mK.CalidLineKV(x,m[x])) by { reveal TCLX, KCLX; }
// }
//
     forall x <- mK.m.Keys ensures mK.CalidLineKV(x,mK.m[x]) //by
     {
//       assert CalidLineKV(x, mK.  m[x]);   //how long?  whu knows
       if (x in m.Keys) {
         assert mK.m[x] == m[x];
         assert this.CalidLineKV(x,m[x]);
         assert x in mK.m.Keys;
         assert CalidLineKV(x,mK.m[x]);   //how long?  whu knows?
         CalidLineKVTo(x,mK.m[x],mK);
         assert mK.CalidLineKV(x,mK.m[x]);
       } else {
         assert x == k;
         assert mK.m[k] == v;
         assert CalidLineKV(k,v); //GNT by { reveal CLKV; } by { reveal CLKV; }
         assert this.CalidLineKV(x,mK.m[x]);
         assert mK.CalidLineKV(x,mK.m[x]);
       }
     }

//      assert (forall k <- mK.m.Keys ::  (k.Ready()));
//      assert (forall k <- mK.m.Keys ::  (mK.objectInKlown(k)));
//      assert (forall k <- mK.m.Keys ::  (var v := mK.m[k]; (v.Ready())));
//      assert (forall k <- mK.m.Keys ::  (var v := mK.m[k]; (v in mK.hns({v}))));
//
//     //  assert mK.thettinGhere();
//     //  assert mK.gettingThere();
//      assert mK.o.Ready();
//      assert mK.objectInKlown(mK.o);
//      assert mK.m.Keys <= mK.oHeap;
//      assert mK.HeapOwnersReady();
//      assert mK.c_amfx <= mK.oHeap;
//
//      assert   (forall k <- mK.m.Keys ::  mK.CalidLineKV(k,m[k]));
//
//      assert mK.AllLinesCalid();
//
//AND THEN IT ALL GETS SIUPER-WEIrD??
//
//      assert (forall k <- mK.m.Keys  ::
//                (var v := mK.m[k];  var o := mK.o;
//                                    && (v.Ready())));
//
//      assert forall o <- mK.m.Values :: o.Ready() ==> ((o.AMFO >= o.AMFB));
//
//      assert (forall k <- mK.m.Keys  ::
//                (var v := mK.m[k];  var o := mK.o;
//                                    && (v.Ready())
//                                    && (v.AMFO >= v.AMFB)
//                ));
//
//      assert (forall k <- mK.m.Keys  ::
//                (var v := mK.m[k];  var o := mK.o;
//                                    && (mK.CalidLineKV(k,v))
//                                    && (not(inside(k,o)) ==> (k == mK.m[k] == v))
//                 // && (not(inside(k,o)) ==> (v.AMFB == k.AMFB))
//                 // && (not(inside(k,o)) ==> (v.AMFO >= v.AMFB == k.AMFB))
//                ));
//
//
//
//      assert (forall k <- mK.m.Keys  ::
//                (var v := mK.m[k];  var o := mK.o;
//                                    && (mK.CalidLineKV(k,v))
//                                    && (not(inside(k,o)) ==> (k == mK.m[k] == v))
//                                    && (not(inside(k,o)) ==> (v.AMFB == k.AMFB))
//                 // && (not(inside(k,o)) ==> (v.AMFO >= v.AMFB == k.AMFB))
//                ));
//
//      assert (forall k <- mK.m.Keys  ::
//                (var v := mK.m[k];  var o := mK.o;
//                                    && (mK.CalidLineKV(k,v))
//                                    && (not(inside(k,o)) ==> (k == mK.m[k] == v))
//                                    && (not(inside(k,o)) ==> (v.AMFB == k.AMFB))
//                                    && (not(inside(k,o)) ==> (v.AMFO >= v.AMFB == k.AMFB))
//                ));
//
//
//
//      assert (forall k <- mK.m.Keys  ::
//                (var v := mK.m[k];  var o := mK.o;
//                                    && (v.Ready())
//                                    && (v.AMFO >= v.AMFB)
//                                    && (not(inside(k,o)) ==> (k == mK.m[k] == v))
//                 // && (not(inside(k,o)) ==> (v.AMFO >= v.AMFB == k.AMFB))
//                 // && (   (inside(k,o)) ==> (v.AMFO >= v.AMFB >= k.AMFB >= o.AMFB))   ///from CalidLineKV
//                 // && (   (inside(k,o)) ==> (v.`owner >= v.bound >= k.bound >= o.bound) )
//                 // && (  mK.m[k].AMFO >= mK.m[k].AMFB >= k.AMFB  )  /// current - early Jun 2025 defiunition from Calid() which soiuld be refacgored
//                ));
//
//      // ///////////////////////////////////////////////////////////////////////////
//
//      // ///////////////////////////////////////////////////////////////////////////
//
//      assert  (forall k <- mK.m.Keys   :: mK.m[k].AMFO >= mK.m[k].AMFB >= k.AMFB) ;
//
// ///assume  (forall k <- mK.m.Keys   :: mK.m[k].AMFO >= mK.m[k].AMFB >= k.AMFB) ;   //WHAT THE FUCK IS THIS DOING HERE
//
//      assert mK.HeapContextReady();
//      assert mK.ValuesContextReady();
//      // ///////////////////////////////////////////////////////////////////////////
//      //tryna get calid
//      assert (mK.Calid())
//      by {
//        assert      && mK.preCalid()
//                    && mK.preCalid2()
//
//                    //calidObjects - mostly about oHeap and ns and stuff
//                    && (mK.m.Keys <= mK.oHeap)
//                    && (forall k <- mK.m.Keys :: (k.Ready() && k.Valid()))
//
//                    //this recapitulates ValuesContextReady() but putting it here lets things work
//                    && (forall v <- mK.m.Values :: (v.Ready() && v.Valid()))
//
//                    //the pivot object "o" being cloned
//                    // && (o.Ready() && o.Valid() && o.Context(oHeap) && objectInKlown(o))
//                    && (mK.o.Ready() && mK.o.Valid() && mK.o.Context(mK.oHeap) && mK.objectInKlown(mK.o))
//
//                    && (forall k <- mK.m.Keys   :: mK.m[k].AMFO  >= mK.m[k].AMFB  >= k.AMFB)
// //wont veruify     && (forall k <- mK.m.Keys   :: mK.m[k].AMFO  >= mK.m[k].AMFB  >= mK.o.AMFB >= k.AMFB)    ///change made then backed out  10JKul 2025 - why wo why oh why ?
// //  WRONG                 && (forall k <- mK.m.Keys   :: mK.m[k].owner >= mK.m[k].bound >= k.bound)
//
//                    && (forall k <- mK.m.Keys   :: (not(inside(k,mK.o)) ==> (mK.m[k] == k)))
//                    && (forall k <- mK.m.Keys   :: (   (inside(k,mK.o)) ==> (mK.m[k] !in mK.oHeap)))
//                    //
//                    //calidSheep - su WRONGbsumed?
//                    //
//                    //see rant aove...
//                    //
//                    //&& (forall k <- mK.m.Keys :: k.fieldModes == mK.m[k].fieldModes)
//                    //
//                    //
//
//                    //KlonVMqpOK(k, context)
//                    && (forall k <- mK.m.Keys :: k.AMFO <= mK.m.Keys)
//                    && (forall k <- mK.m.Keys :: k.AMFB <= mK.m.Keys)
// //                   && (forall k <- mK.m.Keys :: k.bound <= k.owner <= mK.m.Keys)
//                    // && (forall k <- m.Keys :: //;this is s"gettingThere" so why twice?
//                    //      (var v := m[k];
//                    //         && (k.Ready())
//                    //         && (objectInKlown(k))
//                    //         && (v.Ready())
//                    //         && (v in hns())))
//
//                    && (&& (mK.HeapOwnersReady())
//                        && (mK.ValuesOwnersReady())
//                        && (mK.gettingThere())
//                        && (mK.AllLinesCalid()));
//      } //tryna
//
     assert mK.Calid();
     assert mK.SuperCalidFragilistic();
     mK
  )

}
//end CalidKV




  ghost predicate {:isolate_assertions} CKV_preconditions(k : Object, v : Object)
    //attempt to capture the common preconditions for CalidKV

    reads oHeap, m.Values, k, v
    reads m.Keys, m.Values
  {
    && SuperCalidFragilistic()

    && k.Ready() //&& k.Valid() // should context go in here too? probasbly?
    && ownersInKlown(k)   //be nice to get rid of this...
    && o.Ready() //&& o.Valid()
    && objectInKlown(o)

    && CalidCanKey(k)

    && k !in m.Keys
    && v !in m.Values

    // && HeapContextReady()
    // && ValuesContextReady()
    // && Calid()

    && k in oHeap
    && (v.Ready() && v.Valid() && v.Context(hns({v})))

    && this.m.Keys <= this.oHeap

    && klonVMapOK(m)
    && klonCanKV(this, k, v)

    && CalidLineKV(k,v)
  }







  predicate {:isolate_assertions} CalidCanKey(k : Object)
    //conditions an object to be added as a Key into the Klon map
    //  note this doesn't seem to deal with ougoing field values, but that will get
    //  caught eventually via  HeapContextReady() &  ValueContextReady()
    //doesn't seem to require Calid????
    //isn't this more eor less ownersInKlown>?>
    //izn't thgs being replaced ie. tis dead
    requires k.Ready() //&& k.Valid() // should context go in here too? probasbly?
    //requires ownersInKlown(k) ///hmm, req or jsut in body?  Just In BODY!!! 31 Aug 2025

    //pretty sure I want thewe two here to match CalidCanValue
    requires o.Ready() //&& o.Valid()
//    requires objectInKlown(o)  //THAT is clearly FUCKEDy

    reads {}
  {
    && (k in oHeap)
    && (k !in m.Keys)
    && ownersInKlown(k)
  }


  predicate {:isolate_assertions} CalidCanValue(k : Object, v : Object)
    //conditions an object to be added as a Value into the Klon map
    // dunno if I really need this but wrote it anyway as an extenion of CanCalidKey above
    //  note this doesn't seem to deal with ougoing field values, but that will get
    //  caught eventually via  HeapContextReady() &  ValueContextReady()
    //doesn't seem to require Calid????
    requires k.Ready() //&& k.Valid() // should context go in here too? probasbly?
    requires v.Ready() //&& v.Valid()
    requires ownersInKlown(k)
    requires o.Ready() //&& o.Valid()
    requires objectInKlown(o)

    requires CalidCanKey(k)

    //the six requirements of preCalid2 / computeOwnerForClone apocalypse
    requires k.owner <= m.Keys <= oHeap
    requires m.Values <= hns()
    requires o.Ready()
    requires objectInKlown(o)
    requires HeapOwnersReady()
    requires c_amfx <= oHeap

    reads oHeap, m.Values
  {
    && (v !in m.Values)
    && (v.Ready()) //&& v.Valid() && v.Context(hns({v})))
    && (CalidLineKV(k,v)) //will this do?
  }



  ghost predicate {:isolate_assertions} calidCanKV(k : Object, v : Object)
    requires k.Ready() //&& k.Valid() // should context go in here too? probasbly?
    requires v.Ready() //&& v.Valid()
    requires ownersInKlown(k)
    requires o.Ready() //&& o.Valid()
    requires objectInKlown(o)


    reads oHeap, m.Values

  {
    && SuperCalidFragilistic()
    // && HeapContextReady()
    // && ValuesContextReady()
    // && Calid()
    && CalidCanKey(k)
    && CalidCanValue(k,v)
  }




  //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
  //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]




  lemma {:isolate_assertions} CalidLineKVReflexive(k : Object, v : Object)
    //speciefic
    requires not(inside(k,o))
    requires k == v

    //generic?
    requires k.Ready()
    requires ownersInKlown(k)
    requires v.Ready()
    requires o.Ready()
    requires objectInKlown(o)

    //the six requirements of preCalid2 / computeOwnerForClone apocalypse
    requires apoCalidse()

    requires k in oHeap
    requires forall x <- m.Keys :: outside(x,o) ==> (m[x] == x)
//    requires forall x <- k.AMFO :: (m[o] == o)

    ensures  checkOwnershipOfClone(k, v, this)
    ensures  checkBoundOfClone(k, v, this)
    ensures  mappingOwnersThruKlownKV(k,v,this)
    ensures  CalidLineKV(k, v)
  {

    assert forall x <- m.Keys :: outside(x,o) ==> (m[x] == x);

    assert not(inside(k,o));
    assert k == v;
    assert k != o;
    assert k.AMFO == v.AMFO;
    assert checkOwnershipOfClone(k, v, this);
    assert k.owner == v.owner;
    assert k.bound == v.bound;

    k.ExtraReady();

    assert m.Keys >= k.AMFX >= k.AMFB >= k.bound;
    assert m.Keys >= k.AMFX >= k.owner;

    assert outside(k,o);
    //    ExternalOwnersAreOutside(k,o);
    assert forall oo <- k.AMFX  :: outside(oo, o);
    assert forall  x <- m.Keys  :: outside(x, o) ==> (m[x] == x);
    assert forall oo <- k.AMFX  :: m[oo] == oo;
    assert forall oo <- k.owner :: m[oo] == oo;

    assert forall oo <- k.AMFB  :: outside(oo, o);
    assert forall  x <- m.Keys  :: outside(x, o) ==> (m[x] == x);
    assert forall oo <- k.AMFB  :: m[oo] == oo;
    assert forall oo <- k.bound :: m[oo] == oo;

assert v == k;
assert v.bound == k.bound;

    // assert (v.bound == mapThruKlon(k.bound, this));
    // assert (v.owner == mapThruKlon(k.owner, this));

    assert mappingOwnersThruKlownKV(k,v,this);

  }

  //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
  //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]

///OwnersLine version


//Need to WORK The FUCK out wwhat to do about THIS
  ghost predicate {:isolate_assertions}   preOwners() : (r : bool)
    reads oHeap, m.Values
  {
    // && HeapOwnersReady()    ///hmm
    // && ValuesOwnersReady()
    && (o.Ready() && (o in oHeap))
    && (objectInKlown(o))  //progFUCK  do i want this in here? really?   ///Can U do without it??
    && (o.AMFX == o_amfx)
    && (flatten(clbound) >= o.AMFB)
    && (o.AMFO == o_amfx+{o})
    && (c_amfx >= flatten(clbound) >= flatten(o.bound))
  }



  ghost predicate {:isolate_assertions} preOwners2() : (r : bool)
    reads {}
  {
    && (c_amfx <= oHeap) //should goto precalid1??
    && ((o in m.Keys) ==> (
        var c := m[o]; //WE HAS KLONE
        && (c_amfx  == c.AMFX)
        && (clowner == c.owner)
        && (clbound == c.bound)
       ))
  }

  ghost predicate {:isolate_assertions} SuperCalidOwners() : (r : bool)
    reads oHeap, m.Values
  {
    // && HeapOwnersReady()
    // && ValuesOwnersReady()
    && CalidOwners()
  }

  ghost predicate {:isolate_assertions} CalidOwners() : (r : bool)
    // requires  HeapOwnersReady()
    // requires  ValuesOwnersReady()
    reads oHeap, m.Values
  {
        // && HeapOwnersReady()
        // && ValuesOwnersReady()
    && apoCalidse()
    && preOwners()
    && preOwners2()
    && (m.Keys <= oHeap)
    && objectInKlown(o)
    && (forall k <- m.Keys :: OwnersLineKV(k, m[k]))
  }

//does this mean it MUST be in or it CAN be in
//with objectInKnown(k) this says it MUST ne in,. doesn;t it?
//FUCK FUCK FUCK compare CalidLineKV!!!
//ditto (v in hns({v}))) from earlier plain (v in hns())
 predicate {:isolate_assertions} OwnersLineKV(k : Object, v : Object)
    requires apoCalidse()
    reads oHeap, m.Values
  {
//  && (k.Ready() && (objectInKlown(k)) && k in oHeap)   28 Oct 2025
    && (k.Ready() && (ownersInKlown(k)) && k in oHeap)
    && (v.Ready() && (v in hns({v})))

 //   && (v.AMFO  >= v.AMFB  >= k.AMFB)  //GREENLAND
    && (   (inside(k,o)) ==> (k.AMFB  <= o.AMFB))  //GREENLAND

    && (not(inside(k,o)) ==> (v == k))
    && (   (inside(k,o)) ==> ((v !in oHeap)) )

  //MAPPING - progFEARSATAN
    && (mappingOwnersThruKlownKV(k,v,this))
  }


//FROM DAHLIA

lemma {:isolate_assertions} directOwnerInKlownIsEnough(o : Object)
  requires o.Ready()
  requires SuperCalidFragilistic()
  requires o.owner <= m.Keys //note just direct owner
   ensures ownersInKlown(o)
{
  assert forall x <- m.Keys :: objectInKlown(x);
  assert flatten(o.owner) == o.AMFX <= m.Keys;
  assert forall oo <- o.owner :: o.AMFX <= m.Keys;
  assert ownersInKlown(o);
}




  lemma {:isolate_assertions}  FieldFromHeapContext(o : Object, n : string, v : Object)
    //assert a bunch of stuff about a field - could become a function later
    requires HeapContextReady()
    requires o in oHeap
    requires n in o.fields.Keys
    requires v == o.fields[n]

    ensures  v in o.fields.Values
    ensures  v.Ready()
    ensures  v.Valid()
    ensures  v.Context(oHeap)
    ensures  v in oHeap
  {
    assert o.Ready();
    assert o.Valid();
    FieldInFields(o,n,v);
    assert v in o.fields.Values;
    assert o.Context(oHeap);
    assert o.fields.Values <= oHeap;
    assert v in oHeap;
    assert HeapContextReady();
    assert forall x <- oHeap :: (x.Ready() && x.Valid() && x.Context(oHeap));
    assert v.Ready() && v.Valid() && v.Context(oHeap);
  }



}//end datatype Klon
///////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////

///Important Klon Mappinhgs





predicate {:isolate_assertions}  checkOwnershipOfClone(k : Object, v : Object, m : Klon)
  //to work, this needs m.o and m.m[m.o] to be set up
  //but does NOT need k in Keys, or v in values!
  //
  // apparently doesn't even need Caliud or precalid let alone supercalid.  HMMM
  requires k.Ready()
  requires m.ownersInKlown(k)
  requires v.Ready()
  requires m.apoCalidse()

  //the six requirements of preCalid2 / computeOwnerForClone apocalypse
  requires k.owner <= m.m.Keys <= m.oHeap
  requires m.m.Values <= flatten( m.hns() )
  requires m.o.Ready()
  ///requires m.objectInKlown(m.o) //// NO NO NO NO NO NO NO NO NO
  requires m.HeapOwnersReady()
  requires m.c_amfx <= m.oHeap

  reads m.oHeap, m.m.Values
{
  mappingOwnersThruKlownKV(k,v,m)
}




  predicate {:isolate_assertions} mappingOwnersThruKlownKV(k : Object, v : Object, m : Klon) : (r : bool)
    //prog FEAR SATAN
    //this vrsion currently matches CalidLineKV, i.e. k and v don't have to be in the klon
    //but that means we can't mapp intl and AMFO  //um,,
    //i think this is th4e INVARIANT
    //Sure seeems to be the  INVARIANT -- 22 Dec 2025

   decreases k.AMFO
    requires m.apoCalidse()
    requires m.ownersReadyInKlown(k)
//    requires v.Ready()
    reads m.oHeap, m.m.Values
    {
      // prog FEAR SATAN!!

      if (k == m.o) then (
          && (v == m.m[m.o])
          && (v.owner == m.clowner)
          && (v.bound == m.clbound)
        ) else if (outside(k, m.o) )
          then (
            k == v
        ) else (
          assert strictlyInside(k, m.o);
              // && (v.bound == mapThruKlon(k.bound, m))
              // && (v.owner == mapThruKlon(k.owner, m))
              && mappingOWNRsThruKlownKV(k.bound, v.bound, m)
              && mappingOWNRsThruKlownKV(k.owner, v.owner, m)
        )
    }



    //our shold this be MAPPING Owners?????
    //note that this is called ONLY strictly wihin the pivot - see the JDVANCE note
    predicate {:isolate_assertions} mappingOWNRsThruKlownKV(kk : OWNR, vv : OWNR, m : Klon) : (r : bool)
      //actual OWNR version of mappingOwnersThruKlownKV
      //within the pivot anyway!
      //prog FEAR SATAN
          //OK so wher doe this asy "inside the pivot"?   - it DO#ESNT
          //does that matter?  who knows?
      requires m.apoCalidse()
      // requires AllReady(kk)  // 29 Oct 2025
      // requires AllReady(vv)  // 29 Oct 2025
      requires kk <= m.m.Keys
  ////requires vv <= m.m.Values  ///hmm must be trie if kjk,s inside Klon...
  ////requires kk > m.o.AMFO  //gotta be inside kloned bit..  //JDVANCE yeah shoud do that!

        {
//I have NO FUCKING IDEA if this is dong te RIGHT THING or not.
//anin't that great.
//i think its dong CLOSE ENOUGH to the right thing for a paper
//the visualisations all look OK now
//but stil - 21 Sept 2025


        && (vv == (mapThruKlon(kk - m.o.AMFO, m) + m.m[m.o].AMFO))
        && (flatten(kk) <= m.oHeap)
        && (flatten(vv) <= m.hns(vv))

          // var inside1 := kk - m.o.AMFO;
          // var option1 := mapThruKlon(inside1,m) + m.m[m.o].AMFO;
          // (vv == option1)
        }



function {:isolate_assertions} computeOwnerForClone(oo : Owner, m : Klon) : (nuowner : Owner)
  //given some flattened Owner oo, calculate the mapped / cloned version
  //EXCEPT OWNERS SHOULDNT BE FLATTENNED!!!
///TODO//Libertarian  //requires (flatten(oo) >= m.o.AMFO)   //should this be there or not?
  //
  //     7 Aug 2025 - prog thinks - this doesn't work if we're flatting the bound
  //             I removed the constraint hopijng it doesn't break too  much stuff..
  //
  //  I think this makes sense for owners of subparts being clonedj
///  but not neccessarily for e..g bounds that lie (partially) outside?
///
  //  Ha! remember that in many (if not all) cases. bound == owner
  //    which means that, it pretty much needs to have the same mapping...
  //
///seemss to survive without oo being ready!
///seemss to survive without ANYUTHING being Ready
///progA Naa will need Values...
  requires m.apoCalidse()  //note that this requires m.o already in m.m.Keys
  requires oo <= m.m.Keys
//  requires flatten(oo) >= m.o.AMFO //hmmmA
  requires m.SuperCalidFragilistic()
   ensures nuowner <= m.hns()
   ensures flatten(oo) <= m.oHeap //so this MUST be preexisting.
   ensures flatten(nuowner) <= m.hns()
   ensures mappingOWNRsThruKlownKV(oo, nuowner, m)   //rather important
       //yes 'rathr imoportant" infdeed,


   ensures nuowner == global(sideways(local(oo, m),m),m)
 //   ensures nuowner == shiftAMFOZ(oo, m.o.AMFO,  m.m[m.o].AMFO, m.m)

      //********also important that that's OWNRES NOT Owners **************//
      //***ot is it??
      //JDVANCE -- note that sholdlj constraint oo to be inside(the pivot)
      //so the new owner is strictly inside the blivet..../
 // requires flatten(oo) >= m.o.AMFO           //JDVANCE

 reads m.oHeap, m.m.Values
//  reads {}
{
  assert m.ValuesContextReady();
  var inside1 := oo - m.o.AMFO;
  assert inside1 <= m.oHeap;

  var nuowner := mapThruKlon(inside1,m) + m.m[m.o].AMFO;

  assert nuowner == (set x <- (oo - m.o.AMFO) :: m.m[x]) + m.m[m.o].AMFO;
//  assert nuowner == shiftAMFOZ(oo, m.o.AMFO,  m.m[m.o].AMFO, m.m);

  assert mapThruKlon(inside1,m) <= m.m.Values <= m.hns();
  assert m.m[m.o] in m.hns();
  assert m.ValueInContext(m.m[m.o]);
  assert m.m[m.o].AMFO <=  m.hns();

  var fuck1 := local(oo, m);
  var fuck2 := sideways(fuck1, m);
  var fuck3 := global(fuck2, m);
  assert fuck3 == nuowner;

  assert fuck3 == global(sideways(local(oo, m),m),m);


//  .AMFO <= m.m.Values <= m.hns();ƒƒ∂çƒ©
  assert nuowner <= m.hns();
  nuowner
}
//really this is to MATCH the checkClownershipINSIDE



















///////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////

predicate klonVMapOK(m : vmap<Object,Object>, ks : set<Object> := m.Keys)
  requires ks <= m.Keys
  //klonVMapOK the vmap parts of a klon are OK
  //still need to do something for iHeap and ns etc
  //should probably swizzle this to take a Klon, not a vmap/...
  //prog AND that shoud something like klonReady
  //meaning that for all targets (m.Keys)
  //the coresponding klon  m[k] is
  // - ready
  // - corresponds to the target
  //structure of this needs TO MATCH THE CALIDs and
  //object invairants ready, valid, calid, etc
  //klonca
  // IDEALLY the "mapThru" features shouldn't be part of
  // the invariuant itself (klonOK) NOR the extension test (klonCanKV)
  // no the extension (klonKV)
  // rather mapThru etc should be post-derivable efrom calid, not wired in...
  //  which hopefully is ONE clause per "field" of Dahlia's "Object" and no more?
  reads m.Values`fieldModes
  reads ks`fieldModes
{
//Readiness???  //progFEARSATAN
   && (forall k <- ks :: k.Ready() && m[k].Ready() )

  //AMFO
  && (forall k <- ks :: k.AMFO <= m.Keys)
  //  && (forall k <- ks :: mapThruVMap(k.AMFO, m) == m[k].AMFO)

  //AMFB
  && (forall k <- ks :: k.AMFB <= m.Keys)
  //  && (forall k <- ks :: mapThruVMap(k.AMFB, m) == m[k].AMFB)

  //progOWNERS
  //region & owners?
  //  && (forall x <- ks :: x.owaner <= x.AMFO)//progOWNERS
//  && (forall x <- ks :: x.bound <= x.owner <= m.Keys) //should that bound be ks?
  //  && (forall k <- ks :: mapThruVMap(k.owner, m) == m[k].owner)
  //  && (forall k <- ks :: mapThruVMap(k.bound, m) == m[k].bound)

  //field values? //prog
  //
  //
  //  && (forall k <- ks :: k.fieldModes == m[k].fieldModes)
///
  //see rant above
}



  function {:isolate_assertions} {:timeLimit 60} klonKV(m' : Klon, k : Object, v : Object) : (m : Klon)   //TIME-3-OCT
    //aux function for adding k v to a m' giving m
//Klon.CalidKV does all the real work!
  requires k !in m'.m.Keys
  requires v !in m'.m.Values
  requires klonVMapOK(m'.m)
  requires klonCanKV(m', k, v)

  ensures klonVMapOK(m.m)
  ensures klonCanKV(m', k, v)
//  ensures forall x <- m.m.Keys, y <- m.m.Values :: (y == v) ==> (x == k)
  ensures m == m'.(m:=m'.m[k:=v])
  ensures m.from(m')
  ensures m.m.Keys   == m'.m.Keys+{k}
  ensures m.m.Values == m'.m.Values+{v}
  ensures m.o        == m'.o
  ensures m.oHeap    == m'.oHeap
  ensures forall z <- m'.m.Keys :: modesEQ(m'.m[z].fieldModes, m.m[z].fieldModes)

  reads k, v, m'.oHeap, m'.hns(), m'.m.Keys, m'.m.Values

  //   reads k`fields, k`fieldModes
  //   reads v`fields, v`fieldModes
  //
  //   reads m'.oHeap`fields, m'.oHeap`fieldModes
  //   reads m'.ns()`fields,  m'.ns()`fieldModes
    reads m'.m.Keys`fields, m'.m.Keys`fieldModes
    reads m'.m.Values`fields, m'.m.Values`fieldModes

  //reads  m'.m.Values, m'.oHeap  //for ValuesContextReady?
{
  assert klonVMapOK(m'.m);
  assert klonCanKV(m', k, v);
  assert forall x <- m'.m.Keys, y <- m'.m.Values :: (y == v) ==> (x == k);
    // var m'fmodes := map z <- m'.m.Keys :: z := z.fieldModes;
    // assert m'fmodes.Keys == m'.m.Keys;
    // assert forall z <- m'.m.Keys :: modesEQ(z.fieldModes, m'fmodes[z]);

  var r0 : vmap<Object,Object> := vmapKV(m'.m,k,v); // m'.m[k:=v];
  assert klonVMapOK(r0);
  assert r0 ==  m'.m[k:=v];
// assert forall z <- m'.m.Keys :: modesEQ(z.fieldModes, m'fmodes[z]);
// assert forall z <- m'.m.Keys :: modesEQ(r0[z].fieldModes, m'fmodes[z]);

  var r1 := m'.(m:=r0);
  assert r1 == m'.(m:=m'.m[k:=v]);

  haventFuckedFieldModes(m',k,v,r1);

//  assert forall z <- m'.m.Keys :: z.fieldModes == r1.m[z].fieldModes;
  r1
  }

//
// //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//

predicate modesEQ(a : map<string,Mode>, b : map<string,Mode>)
 { (a.Keys == b.Keys) && (forall n <- a.Keys :: a[n] == b[n]) }


  lemma {:isolate_assertions} {:timeLimit 30} haventFuckedFieldModes(m' : Klon, k : Object, v : Object, m : Klon)
    requires k !in m'.m.Keys
    requires v !in m'.m.Values
    requires klonVMapOK(m'.m)
    requires klonCanKV(m', k, v)
    requires m == m'.(m:=m'.m[k:=v])
     ensures forall z <- m'.m.Keys :: modesEQ(m'.m[z].fieldModes, m.m[z].fieldModes)
{
    var m'fmodes := map z <- m'.m.Keys :: z := m'.m[z].fieldModes;
    assert m'fmodes.Keys == m'.m.Keys;
    assert forall z <- m'.m.Keys :: modesEQ(m'.m[z].fieldModes, m'fmodes[z]);
    assert forall z <- m'.m.Keys :: modesEQ(m. m[z].fieldModes, m'fmodes[z]);
    assert forall z <- m'.m.Keys :: modesEQ(m'.m[z].fieldModes, m.m[z].fieldModes);
}

//
//
//
// //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//

predicate klonCanKV(m' : Klon, k : Object, v : Object)
  //extending m' with k:=v will be klonVMapOK
  // requires klonVMapOK(m'.m)  //should this be here?  if not, in below!  //BOWIE

  //requires m'.HeapContextReady()     //wuld be nice but fucks callers' read clauses?
  //requires m'.ValuesContextReady()
  //requires Calid() ?????

///does not check ownerhsip!!!

  reads k, v, m'.oHeap, m'.hns(), m'.m.Keys, m'.m.Values
  // reads k`fields, k`fieldModes
  // reads v`fields, v`fieldModes
  //
  // reads m'.oHeap`fields, m'.oHeap`fieldModes
  // reads m'.ns()`fields,  m'.ns()`fieldModes
  // reads m'.m.Keys`fields, m'.m.Keys`fieldModes
  // reads m'.m.Values`fields, m'.m.Values`fieldModes
{
  && klonVMapOK(m'.m) //BOWIE
  && canVMapKV(m'.m, k, v)
  && (k in m'.oHeap)  //prog do I want this here?
  && (if (v==k) then (v in m'.oHeap) else (v !in m'.oHeap)) //nope - happens after  wards

  //grrr. should refactor this
  && k.Ready() && k.Valid() && k.Context(m'.oHeap)
  && v.Ready() && v.Valid() && v.Context(m'.hns({v}))

  //  && k.Context(m'.m.Keys+{k})  ///what IS this?
  &&  m'.ownersInKlown(k)
  && (k.fieldModes == v.fieldModes)//hhhmm see anbove

  //  && (v.AMFX >= v.AMFB >= k.AMFB) //is this right?   really?
  //17 June 2025 prog thinks this iswrong & shoud be in CalidLineKV


  //END DOOUBLE BOWIE
}

// basic mappings


function {:isolate_assertions} mapThruKlon(os: set<Object>, m : Klon) : (r : set<Object>)
  //image of os under klon mapping m
  // reads m.m.Keys`fields, m.m.Keys`fieldModes
  // reads m.m.Values`fields, m.m.Values`fieldModes
  requires os <= m.m.Keys
   ensures r  <= m.m.Values
   ensures (os > {}) ==> (r > {})
  reads {}
    { assert (os > {}) ==> ( var x :| x in os; {m.m[x]} > {});  //THIS LINE IS OF SATAN. WASBN"T NEEDED PREVIOUSLY.,..
      set o <- os :: m.m[o] }

function mapBackKlon(os: set<Object>, m : Klon) : (r : set<Object>)
  //image of os under INVERSE klon mapping m
  // reads m.m.Keys`fields, m.m.Keys`fieldModes
  // reads m.m.Values`fields, m.m.Values`fieldModes
  requires os <= m.m.Values
  ensures  r  <= m.m.Keys
  reads {}
{ mapBackVMap(os,m.m) }

function objThruKlon(o : Object, m : Klon) : Object    requires o in m.m.Keys {m.m[o]}






predicate {:isolate_assertions} istKlonnyKlon(os : Owner, ks : set<Object>, m : Klon)
    requires m.o.Ready()
    requires m.objectInKlown(m.o)
    requires os <=  m.m.Keys <= m.oHeap
    requires m.c_amfx <= m.oHeap
    requires m.apoCalidse()
    requires m.SuperCalidFragilistic()

     reads m.oHeap, m.m.Values

    decreases os, 50
{
  && (forall o <- os :: o in m.m.Keys)
  && (m.o in os)
  && (computeOwnerForClone(os, m) == ks)  ///AMOST CERTAINLY WRONG!!!!!  --- should call checkOwnershipOfClone instead
}

predicate istKlonAlleFelder(o : Object, k : Object, m : Klon)
  reads o`fields, o`fieldModes
  reads k`fields, k`fieldModes
{
  && (o.fields.Keys     == k.fields.Keys)
  && (o.fieldModes.Keys == k.fieldModes.Keys)
  && (o.fields.Values     <= m.m.Keys)
  && (forall f <- o.fields.Keys :: (m.m[o.fields[f]]  == k.fields[f]))
//  && ()   //at some point needs to check mapping for fieldModes?    //OR NOT///
}


///// special purpose mappings - local/globa/sideways

function local(o : OWNR, m : Klon) : (r : OWNR)
 //take a "global" original OWNR to a local internal one in the original (should this be global2local)
 //should theyb e differen types? ARGH!
  // //requires isFlat(o)
  // //ARGH.  this is a set of Owners inside the pivotg
  // //but those objects are all fully global AMDOs...?
  // requires m.apoCalidse()
  // requires o >= m.o.AMFO   //o >= or o > ?
   ensures r <= o
   //ensures isFlat(r)
   // { o - m.o.AMFO  }   //shit shit shit
   { o - m.o.AMFO  }

function {:isolate_assertions} global(oo : set<Object>, m : Klon) : (rs : set<Object>)
 //take a "local" OWNR to a global one in the clone (should this be local2global)
   requires m.apoCalidse()
  //  requires forall o <- oo :: inside(o,m.m[m.o])
  //  //ensures  isReallyFuckingFlat(rs)
  // //requires o >= m.o.AMFO
  //  //ensures isFlat(r)
   { oo + m.m[m.o].AMFO  }

function sideways(oo : set<Object>, m : Klon) : (r : set<Object>)
 //take a "local" OWNR to a global one in the clone (should this be local2global)
  //  requires AllReady(oo)
   requires oo <= m.m.Keys
  //  requires m.apoCalidse()
  // //requires isFlat(o)
  // requires oo <= m.o.AMFO
  //  //ensures isFlat(r)
  ensures r ==  mapThruKlon(oo, m) //hmm???
  ensures r <= m.m.Values
   { mapThruKlon(oo, m) }














predicate checkBoundOfClone(k : Object, v : Object, m : Klon) { nuBoundsOK(k.owner, k.bound) }
