include "Library.dfy"
include "Mode.dfy"
include "Ownership.dfy" //comes in via Mode anyway..

//TODOS when valid - precondition on comoputeWOwnerForClone - see JDVANCE
//GREENLAND   - geting bound covariant over cloning
//AMDI_FINT   - whther refDI (f.AMFO == t.AMFX) or  (f in t.owner)
//AMFB_GEQ_GT - whether refBI should be >= or > --- I dunno how refBI fuckswith CalidLineKVTo but it seedms to...
//THULE - shit that depends on e.g  mtk(m.o.AMFO) == m.m[m.o].AMFO o
//         or the lesser mtk(m.o.owner) == m.m[m.o].owner
//NUBOUND -  using nuBound instead of collectbound ;-)
  //Beady2() more bounds shit
  //AMFB-NOT-NULL null  bound bans outgoing references
//REVERT - revertig defintion of flatten to have the extra +os (and so tolerate un-Ready() arguments)
//Libertarin - input constraints on computeOwnershiOfClone
//verifies clear 25 Jan 2025

type Owner = set<Object>

type OWNR  = Owner // except OWNRs should be flattened

//these types are declared mostly so "printing" can be linked in (or not)
// datatype Edge = Edge(f : Object, n : string, m : Mode, t : Object)
// type Incoming = map<Object,set<Edge>>

class Object {

  const bound : Owner //movement bound - stands in for explcit owner parameters
  const AMFB  : OWNR  //flattened bound

  const owner : Owner//actual "dynamic" Owner owner of this objectq --- *XTERNAL*
  const AMFX :  OWNR //flattened owner  /// aka all externeal owners

  const self  : Owner //internal owners - i.e. Self-ownership - i.e. includers THIS
  const AMFO  : OWNR  //All MY FUCKING Owner  (aka All My Flat Owner:-)


  var   fields     : map<string,Object>//field values. uninit fields have no entries
  var   fieldModes : map<string,Mode>//Mode of each field name -  note, static! - would be statically known by any methods

  var   nick : string //nickname


//LILLE constructor arguments
  constructor {:isolate_assertions} {:timeLimit 20} make(ks : map<string,Mode>, oo : Owner, context : set<Object>, name : string, mb : Owner := froposeBounds(oo))
    //make an object.  owner & (opt) bound should be local owners, not flattened OWNRS

//refactored 30 Jan 2026!! //bunch of commented-out-stuff excised

    requires context >= flatten(oo) >= flatten(mb)   //GRR
    requires flatten(oo) >= flatten(mb)
    requires forall o <- flatten(oo) :: o.Ready()
    requires nuBoundsOK(oo, mb)   ///attempting to get verification times down
//    requires myBoundsOK(oo, mb)   ///attempting to get verification times down

//"rephrase" precondtions
    ensures context >= AMFX >= AMFB
    ensures forall o <- AMFX :: o.Ready()
    ensures nuBoundsOK(owner, bound)

//export main variable values
    ensures bound == mb
    ensures owner == oo
    ensures fields == map[]
    ensures fieldModes == ks
    ensures nick == name


 //correctness invariants etc
    ensures Ready()
    ensures Valid()
    ensures context+{this} >= AMFO   //do I need on plus the one below?
    ensures Context(context+{this}) //only possible cos we go no fields?
    ensures unchanged( context )
    ensures fresh(this)
    modifies {}
  {
    bound       := mb;
    owner       := oo;
    self        := owner + {this};
    self        := self;

    AMFB        := flatten(mb);
    AMFX        := flatten(oo);
    AMFO        := flatten(oo)+{this};

    fieldModes  := ks;
    fields      := map[];
    nick        := name;

    new;

    assert initialValues(ks,oo,name,mb);

    MakeOwnerOwners(oo, mb);
    MakeOwnerSelfies(oo,mb);
    MakeInContext(context);
    assert unchanged( context );
  }


predicate {:isolate_assertions} Ready()
    //well-formdness of ownership
    reads {}
    decreases AMFO, 20
  {
    && (self  == owner +  {this})
    && (AMFB == flatten(bound))
    && (AMFX == flatten(owner))
    && (AMFO == flatten(self ))
    && (AMFO == AMFX + {this})
    && (isFlat(AMFB))
    && (isFlat(AMFO))
    && (isFlat(AMFX))
    && (AMFO > AMFX >= AMFB)
    && (forall oo <- AMFX  :: (AMFO > oo.AMFO) && oo.Ready())
//    && (forall oo <- owner :: AMFB <= oo.AMFB)  //Beady2()
    //NUBOUND
  //  && (nuBoundsOK(owner, bound))

    && (myBoundsOK(owner, bound))

    && (this !in AMFX) && (this !in owner) &&  (this !in bound)
  }

lemma {:isolate_assertions} ExtraReady()
   //consequences of well-formedness (Ready) that dafny cant always find easily
  decreases AMFO
    requires Ready()

    ensures isFlat(AMFB)
    ensures isFlat(AMFX)
    ensures isFlat(AMFO)

    ensures flatten({this}) == AMFO

    ensures  this !in bound
    ensures  this !in owner
    ensures  this  in self
    ensures  this !in AMFB
    ensures  this !in AMFX
    ensures  this  in AMFO

    ensures  forall oo <- AMFX :: (outside(oo,this))
    ensures  forall oo <- AMFB :: (outside(oo,this))

    ensures  AMFO >= owner
    ensures  AMFO >= bound

    ensures  (forall oo <- self   :: AMFO >=  oo.AMFO)
    ensures  (forall oo <- owner  :: AMFO >   oo.AMFO)
    ensures  (forall oo <- AMFX   :: AMFX >=  oo.AMFO)
    ensures  (forall oo <- AMFX   :: AMFX >   oo.AMFX)
    ensures  (forall oo <- AMFX   :: this !in  oo.AMFO)
    ensures  (forall oo <- AMFX   :: this !in  oo.AMFX)
    ensures  (forall oo <- AMFX   :: AMFO >    oo.AMFO)
    ensures  (forall oo <- AMFO   :: AMFO >=   oo.AMFO)

    ensures  (forall o  <- AMFO ::  AMFO >= o.AMFO)
    ensures  (forall o  <- AMFX, ooo <- o.AMFX :: AMFX >= o.AMFX >= ooo.AMFX)
    ensures  (forall o  <- AMFO, ooo <- o.AMFO :: AMFO >= o.AMFO >= ooo.AMFO)

    ensures  (forall oo <- owner :: inside(this, oo))

//extra readiness
    ensures  (forall oo <- owner   :: oo.Ready())
    ensures  (forall oo <- bound   :: oo.Ready())

    ensures  (forall oo <- AMFX   :: oo.Ready())
    ensures  this.Ready()  //really?  really really??
    ensures  (forall oo : Object <- AMFX+{this}   :: oo.Ready())
    ensures  (forall oo <- AMFO   :: oo.Ready())



//bounds

ensures nuBoundsOK(owner, bound)
ensures forall o <- owner :: nuBoundsOK(o.owner, o.bound)

//outside
    ensures  (forall x : Object | outside(this,x)     :: forall oo : Object <- AMFO  :: outside(oo,x))
    ensures  (forall x : Object | outside(this,x)     :: forall oo : Object <- owner :: outside(oo,x))
    ensures  (forall x : Object | outside(this,x)     :: forall oo : Object <- bound :: outside(oo,x))

    ensures  (forall x : Object | not(inside(this,x)) :: forall oo : Object <- AMFO  :: not(inside(oo,x)))

  {
    assert flatten(owner) == AMFX;
    assert flatten({this}) == AMFO;

    assert  (forall o  <- AMFX :: o.Ready());
    assert  (forall o  <- AMFX, ooo <- o.AMFX :: ooo.Ready());
    forall  o <- AMFX ensures (true) { o.ExtraReady(); }

    assert AMFO == AMFX + {this};
    assert this.Ready();

    assert  (forall o  <- AMFX ::  AMFX >= o.AMFX);
    assert  (forall o  <- AMFX ::  AMFX >  o.AMFX);
    assert  (forall o  <- AMFX ::  this !in o.AMFO);

    assert  (forall o  <- AMFO ::  AMFO >= o.AMFO);
    assert  (forall o  <- AMFX ::  AMFO >  o.AMFO);

    assert  (forall o  <- AMFX, ooo <- o.AMFX :: AMFX >= o.AMFX >= ooo.AMFX);
    assert  (forall o  <- AMFX, ooo <- o.AMFX :: AMFO >  o.AMFO >  ooo.AMFO);

    Aux_nest_AMFO(this);
    assert (forall oo <- AMFO, ooo <- oo.AMFO :: AMFO >= oo.AMFO >= ooo.AMFO);

  }

lemma Aux_nest_AMFO(o : Object)
  //helper - AMFOs nest.
  requires o.Ready()
  ensures  (forall oo <- o.AMFO, ooo <- oo.AMFO :: o.AMFO >= oo.AMFO >= ooo.AMFO)
{}

/////////////////////////////////////////////////////////////////////////////////////////////


 predicate initialValues(ks : map<string,Mode>, oo : Owner, name : string, mb : Owner)
  //helper to make
  reads  this`fieldModes, this`fields, this`nick
 {
    && (bound      == mb)
    && (owner      == oo)
    && (self       == owner + {this})
    && (self       == self)
    && (AMFB       == flatten(mb))
    && (AMFX       == flatten(oo))
    && (AMFO       == flatten(oo)+{this})
    && (AMFO       == AMFX + {this})
    && (fieldModes == ks)
    && (fields     == map[])
    && (nick       == name)
 }


lemma MakeOwnerOwners(oo : Owner, mb : Owner)
  //helper to make
  requires flatten(oo) >= flatten(mb)
  requires forall o <- flatten(oo) :: o.Ready()
  requires nuBoundsOK(oo, mb)

  requires owner == oo
  requires bound == mb
  requires self  == owner + {this}
  requires self  == self

  requires AMFB  == flatten(mb)
  requires AMFX  == flatten(oo)
  requires AMFO  == AMFX + {this}

   ensures forall oo <- AMFX :: oo.Ready()
   ensures AMFO > AMFX >= AMFB
   ensures forall oo <- AMFX :: AMFO > oo.AMFO
   ensures nuBoundsOK(oo, mb)
  {}


lemma MakeOwnerSelfies(oo : Owner, mb : Owner)
  //helper to make

  requires flatten(oo) >= flatten(mb)
  requires forall o <- flatten(oo) :: o.Ready()
  requires nuBoundsOK(oo, mb)

  requires owner == oo
  requires bound == mb
  requires self  == owner + {this}
  requires self  == self

  requires AMFB  == flatten(mb)
  requires AMFX  == flatten(oo)
  requires AMFO  == AMFX + {this}

   ensures AMFO  == flatten(oo)+{this}
   ensures AMFO  == flatten(self)
   ensures nuBoundsOK(oo, mb)
    {
        MakeOwnerOwners(oo, mb);
        assert self == owner + {this};
        assert flatten(self) == flatten(owner+{this});
        assert AMFO == AMFX + {this};
        assert flatten({this}) == this.AMFO;
        assert flatten(owner) + flatten({this}) == flatten(owner + {this});
        assert flatten(self) == this.AMFO;

  }

  lemma {:isolate_assertions}    MakeInContext(context : set<Object>)
  //helper to make
   requires Ready()
   requires context >= flatten(owner)
   requires fields == map[]
    ensures Context(context+{this})
{
      assert Ready();
      assert (this in context+{this});
      assert context >= flatten(owner);
      assert context+{this} >= flatten(owner)+{this};
      assert flatten(owner)+{this} == AMFO;
      assert (context+{this} >= AMFO);

      assert fields == map[];
      assert fields.Keys == {};
      assert fields.Values == {};
      assert Valid();
 }


  predicate Valid()
    //invariant over mutable state (fields) of THIS object
    reads this`fields, this`fieldModes
    decreases AMFO
  {
      //some comments here cos some earlier seperate things were inlined.
    && Ready()
//NO_FIELDMODES       && (fields.Keys <= fieldModes.Keys)
                //aka AllFieldsAreDeclared()
    && (forall n <- fields :: refOK(this, fields[n]))
               //sortof AllOutgoingReferencesAreOwnership(…)
//NO_FIELDMODES       && (forall n <- fields :: modeOK(this, fieldModes[n], fields[n]))
               //aka AllFieldsContentsConsistentWithTheirDeclaration()
  }

predicate FieldValidNV(n : string, v : Object)
  //is v a valid value for field n?
  //should work whether or not v is currently the field value
    reads this`fields, this`fieldModes
{
//NO_FIELDMODES           && (n in fieldModes.Keys)
    && (refOK(this, v))
//NO_FIELDMODES           && (modeOK(this, fieldModes[n], v))
}

  predicate OwnersWithin(context : set<Object>)
    decreases AMFO
        reads {}
   {Ready() && (context >= AMFO)}  //OPT just AMFO    && (context >= AMFB)


lemma WhereOwnersGoBoundsHaveGone(os : set<Object>)
  requires Ready()
  requires AMFO <= os
   ensures AMFB <= os
{}


  predicate Context(context : set<Object>) : (rv : bool)
    //Object's owners *and fields* are within this context
    reads this`fields, this`fieldModes
    decreases AMFO
    ensures (rv ==> (context >= AMFO))
    ensures (rv ==> (context >= fields.Values))
  {
    && Ready()    //29 Jan 2026 FUCKY FUCKY FUCK    //REVERT 2 Feb 2026
    && Valid()   //29 Jan 2026 FUCKY FUCKY FUCK    //REVERT 2 Feb 2026
    && (this in context)
    && (context >= AMFO)
    && (context >= fields.Values)   //this the last one that's the kicker.
  }

  lemma WiderContext(less : set<Object>, more : set<Object>)
    requires less <= more
    //  requires Ready()
    requires Context(less)  //Context doesnt require Ready, it incorporates it...
     ensures Context(more)
  {}

  function ValidReadSet() : set<Object>  //LILLE perhaps
    reads this`fields, AMFO`fields
  {
  {this} + fields.Values + AMFO +
      (set o1 <- AMFO, o2 <- o1.fields.Values :: o2) //JESUS MARY AND JOSEPH AND THE WEE DONKEY
  }


//accessors
  function outgoing() : set<Object> reads this`fields { fields.Values }
  function fieldNames() : set<string> reads this`fields { fields.Keys }    //WAS {  fieldModes.Keys }
  function size() : nat reads this`fields { |outgoing()| }

  function allExternalOwners() : set<Object> { AMFX }
  function allExternalBounds() : set<Object> { AMFB }

  predicate AllFieldsAreDeclared() reads this`fields, this`fieldModes
   //NO_FIELDMODES   { fields.Keys <= fieldModes.Keys }
   { true }

  predicate AllFieldsContentsConsistentWithTheirDeclaration()
    requires AllFieldsAreDeclared()
    reads this`fields, this`fieldModes
    { true }
   //   forall n <- fields :: AssignmentCompatible(this, fieldModes[n], fields[n])

  predicate AllOutgoingReferencesAreOwnership(os : set<Object>)
    reads this`fields//, fields.Values,  os//semi-evil
    requires Ready() // ||  TRUMP()
    //requires forall n <- fields :: ownersOK(fields[n],os)
    { forall n <- fields :: refOK(this, fields[n]) }


  predicate AllOutgoingReferencesWithinThisHeap(os : set<Object>)
    reads this`fields
    { outgoing() <= os }


predicate AllFieldsValid()
    reads this`fields, this`fieldModes
    {forall n <- fields :: FieldValidNV(n, fields[n])}

lemma ValidMeansAllFieldsValid()
  requires Ready()
  ensures Valid() <==> (forall n <- fields :: FieldValidNV(n, fields[n]))
  ensures Valid() <==> AllFieldsValid()
{}

  method usetf(n : string, v : Object)
    requires Ready()
    requires n  in fieldModes.Keys
    requires refOK(this, v)
     ensures fields == old(fields)[n:=v]
    modifies this`fields
       { fields := fields[n:=v]; }

  function ugetf(n : string) : (v : Object)
    requires n in fieldModes.Keys
    requires n in fields.Keys
       reads `fields, `fieldModes
       { fields[n] }

  method {:isolate_assertions} setf(n : string, v : Object)
    requires Ready()
    requires Valid()
//NO_FIELDMODES         requires n  in fieldModes.Keys
    requires refOK(this, v)
 //   requires v.Ready()  //READYREADY
    //NO_FIELDMODES         requires forall n <- fields :: (n in fieldModes) && modeOK(this, fieldModes[n], fields[n])
    //NO_FIELDMODES             requires modeOK(this, fieldModes[n], v)
    requires v.bound == v.owner //OWNERBOUND
     ensures fields == old(fields)[n:=v]
     ensures refOK(this, fields[n])
     ensures ownerf(n, v.owner)
     ensures Valid()
     ensures forall n <- fields :: (n in fieldModes) && modeOK(this, fieldModes[n], fields[n]) //OWNERBOUND
    modifies this`fields
       { fields := fields[n:=v];
         assume n in fieldModes.Keys; //OWNERBOUND
         assume modeOK(this, fieldModes[n], v); //OWNERBOUND
         assume forall n <- fields :: (n in fieldModes) &&  modeOK(this, fieldModes[n], fields[n]); //OWNERBOUND
        }

  function getf(n : string) : (v : Object)
//NO_FIELDMODES    requires n in fieldModes.Keys
        requires n in fields.Keys
       ensures v.owner == v.bound //OWNERBOUND
       ensures v.Ready() //READYREADY
       reads `fields, `fieldModes
       { assume {:axiom} n in fields.Keys;  //NO_FIELDMODES
         assume fields[n].owner == fields[n].bound; //OWNERBOUND
         assume fields[n].Ready(); //READYREADY
           fields[n] }

   predicate ownerf(n : string, oo : Owner)
       //does field n have owner oo?   (and - for now -  is it accessible from me?)
       reads `fields, `fieldModes
       {&& (n in fields.Keys)
        && (fields[n].owner == oo)
        && (fields[n].bound == oo)  //OWNERBOUND
        && (refOK(this,fields[n]))
        //NO_FIELDMODES      shioujdl be a mode check here too I guess??
        && ((fields[n].owner == oo) == (fields[n].owner == oo)) }  //OWNERBOUND

        // lemma {:isolate_assertions} I_HATE_BOUNDS()
//   requires Ready()
//    ensures ( (set ooo : Object <- {this}, omb : Object <-  ooo.AMFB :: omb) + {this} ) == (AMFB + {this})
//    ensures (forall oo <- owner :: oo.AMFB >= AMFB)
//  {
//   calc {
//      (set ooo : Object <- {this}, omb : Object <-  ooo.AMFB :: omb) + {this};
//      (set                         omb : Object <- this.AMFB :: omb) + {this};
//      (                                                 AMFB       ) + {this};
//      AMFB + {this};
//    }
//    assert (AMFO > AMFX >= AMFB);
//    assert flatten(bound) == AMFB;
//    assert flatten(owner) == AMFX;
//    assert flatten(owner) + {this} == AMFO;
//    assert flatten(owner) >= flatten(bound);
//
//    assert this !in AMFX;  assert this !in AMFB;
// }


function collectOwnersBounds() : set<set<Object>>  { set o <- owner :: o.AMFB }

function proposeOwnerRebound() : set<Object> { intersetion( collectOwnersBounds() ) }
//
// lemma {:isolate_assertions} {:timeLimit 20} Bounds_Reflexive(oo : Owner)
//    requires forall o <- oo :: o.bound == o.owner
//    requires AllReady(oo)
//   //  ensures nuBoundsOK(oo, oo)
//     ensures intersetion({oo}) == oo
//
//   {
//     forall o <- oo ensures (true) { o.ExtraReady(); }
//     assert forall o <- oo :: o.AMFX == o.AMFB;
//     assert forall o <- oo :: flatten(oo) >= o.AMFO > o.AMFX == o.AMFB;
//
//     var set_of_owners_bounds : set<set<Object>> := set o <- oo :: o.AMFB;
//     assert set_of_owners_bounds == set o <- oo :: o.AMFX;
//
//     var interset_bounds : set<Object> := intersetion( set_of_owners_bounds );
//     assert interset_bounds == intersetion( set o <- oo :: o.AMFB );
//     assert interset_bounds == intersetion( set o <- oo :: o.AMFX );
//
//
//     assert forall o <- oo :: o.AMFB >= interset_bounds;
//
//   assert (flatten(oo) >= flatten(oo)) ; //aka effectiveowner is INSIDE effectivebound
//   assert (forall o <- oo :: o.AMFB >= flatten(oo)) ;
//
//   }


  method {:isolate_assertions} usetn(n : string, v : nat)
    requires Ready()
    requires Valid()
    requires (forall n <- fields :: (n in fieldModes) && modeOK(this, fieldModes[n], fields[n]))
    requires n in fieldModes.Keys
    requires fieldModes[n] in {Evil} //Rep too?
     ensures fields.Keys == old(fields.Keys) + {n}
     ensures Ready()
     ensures Valid()
    modifies this`fields
       {
         var vBnd := proposeBounds({this});
         var vObj := new Object.make(map[],{this},AMFO, natToString(v), vBnd);
         assert refOK(this, vObj);
         fields := fields[n:=vObj];
         assert Ready();
         assert (forall n <- fields :: refOK(this, fields[n]));
         MODE_INDIGO(this ,fieldModes[n], vObj);
         assert (forall n <- fields :: (n in fieldModes) && modeOK(this, fieldModes[n], fields[n]));
       }



  function ugetn(n : string) : (v : nat)
    requires n in fieldModes.Keys
    requires n in fields.Keys
       reads `fields, `fieldModes, fields.Values`nick
       { var vObj := fields[n];
         if (forall c <- vObj.nick :: c in "0123456789")
           then (stringToNat(vObj.nick))
           else 0 }



  method {:isolate_assertions} uincrn(n : string)
    requires Ready()
    requires Valid()
//NO_FIELDMODES    requires n in fieldModes.Keys
//NO_FIELDMODES    requires n in fields.Keys
//NO_FIELDMODES    requires fieldModes[n] in {Evil}
     ensures fields.Keys == old(fields.Keys) + {n}
     ensures forall k <- old(fields.Keys) | k != n :: fields[k] == old(fields[k])
     ensures Ready()
     ensures Valid()
    modifies this`fields
       {
         assume {:axiom} n in fields.Keys;  //NO_FIELDMODES
         var val := getn(n) + 1;
         setn(n, val);
       }


  method {:isolate_assertions} setn(n : string, v : nat)
    requires Ready()
    requires Valid()
//NO_FIELDMODES    requires n in fieldModes.Keys
//NO_FIELDMODES    requires fieldModes[n] in {Evil}  //Rep too?
     ensures fields.Keys == old(fields.Keys) + {n}
     ensures forall k <- old(fields.Keys) | k != n :: fields[k] == old(fields[k])
     ensures Ready()
     ensures Valid()
    modifies this`fields
       {
         var vBnd := proposeBounds({this});
         var vObj := new Object.make(map[],{this},AMFO, natToString(v), vBnd);
         assert refOK(this, vObj);
         fields := fields[n:=vObj];
         assert Ready();
         assert (forall n <- fields :: refOK(this, fields[n]));
 assume {:axiom} n in fields.Keys;  //NO_FIELDMODES
//NO_FIELDMODES          MODE_INDIGO(this ,fieldModes[n], vObj);
// assume (forall n <- fields :: modeOK(this, fieldModes[n], fields[n]));
    assume Valid();  // //NO_FIELDMODES ??
       }

  method {:isolate_assertions} incrn(n : string)
    requires Ready()
    requires Valid()
//NO_FIELDMODES    requires n in fieldModes.Keys
//NO_FIELDMODES    requires n in fields.Keys
//NO_FIELDMODES    requires fieldModes[n] in {Evil}
     ensures fields.Keys == old(fields.Keys) + {n}
     ensures forall k <- old(fields.Keys) | k != n :: fields[k] == old(fields[k])
     ensures Ready()
     ensures Valid()
    modifies this`fields
       {
         assume {:axiom} n in fields.Keys;  //NO_FIELDMODES
         var val := getn(n) + 1;
         setn(n, val);
       }


  function getn(n : string) : (v : nat)
//NO_FIELDMODES    requires n in fieldModes.Keys
//NO_FIELDMODES    requires n in fields.Keys
       reads `fields, `fieldModes, fields.Values`nick
       {
//NO_FIELDMODES assume n in fields.Keys
         assume {:axiom} n in fields.Keys;  //NO_FIELDMODES
          var vObj := fields[n];
         if (forall c <- vObj.nick :: c in "0123456789")
           then (stringToNat(vObj.nick))
           else 0 }


  predicate isf(n : string)
   //is field n set on this object?
//NO_FIELDMODES    requires n in fieldModes.Keys //yuck
    reads `fields, `fieldModes, fields.Values`nick
       { n in fields.Keys }




}//end class Object

 function fields(fs : set<string> ) : map<string,Mode>  { map f <- fs :: f := Evil }

  lemma {:isolate_assertions} FieldInFields(o : Object, n : string, v : Object)
    requires o.Ready()
    requires o.Valid()
    requires n in o.fields.Keys
    requires v == o.fields[n]
    ensures  v in o.fields.Values
  {}



function intersetion<T>(intersets : set<set<T>>) : set<T>
 {
  set s : set<T> <- intersets, e : T <- s | (forall t : set<T> <- intersets :: e in t ) :: e
 }

// lemma {:isolate_assertions} {:timeLimt 0} AllForOneAndOneForALl(oo : Owner, mb : Owner)
//   requires AllReady(oo)
//   requires  mb == intersetion( set o <- oo :: o.AMFB )
//    ensures forall x <- mb, t <- oo :: x in t.AMFB
//   {}

// function recIntersectAll (intersets : set<set<T>>) : set<T>
//  // return a set of only the elements in all other sets
//  {
//     if (intersets == {})
//        then ({})
//        else (  if (|interests| == 1) then (interests)
//            else ( if (|interests| == 2) then (
//                 var l :| l in intersects;
//                 var r :| r in  intersects && r != l ;
//
//
//            )
