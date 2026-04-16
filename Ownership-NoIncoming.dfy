  include "Ownership-Lemmata.dfy"

lemma {:isolate_assertions} NoIncomingPointers(f : Object, o : Object, t : Object)
  requires f.Ready() && o.Ready() && t.Ready()

  requires strictlyInside(t,o)
  requires outside(f,o)
 // requires outside(t,f)

   ensures not(refOK(f,t))
{}



lemma {:isolate_assertions} NoOutgoingPointers(f : Object, o : Object, t : Object)
  requires f.Ready() && o.Ready() && t.Ready()

  requires o.owner != o.bound
  requires o.bound == {}
   ensures o.ownerBound() == {}

  requires strictlyInside(f,o)
  requires outside(t,o)

   ensures not(refOK(f,t))
{
  assert f != t;
  assert not(inside(t,f));

  OneNilAMFO(f,o);
  assert not(f.AMFB > {});
  assert not(refOK(f,t));

}





lemma {:isolate_assertions} MovingOnUp(f : Object, o : Object, oo  : Object, t : Object)
  requires f.Ready() && o.Ready() && t.Ready() && oo.Ready()

  requires refOK(o,t)
  requires strictlyInside(o,oo)
  requires outside(t,o)
   ensures o.AMFO >  oo.AMFO
  requires o.AMFB <= oo.AMFB //contravariant --- can I get soemthing close to this directly (answer: not with ownerBounds?)
   ensures refOK(oo,t)
{
    TransitiveBounds(o,oo);
}




lemma {:isolate_assertions} MovingOnDown(f : Object, o : Object, t : Object)
  requires f.Ready() && o.Ready() && t.Ready()

  requires refOK(o,t)
  requires strictlyInside(f,o)
  requires outside(t,o)
  requires f.AMFB == o.AMFB
   ensures refOK(f,t)
{}




lemma Goop(f : Object, t : Object)
  requires f.Ready() && t.Ready()
  requires t.owner == {f}
   ensures t.AMFX  == f.AMFO
   {}

lemma {:isolate_assertions} NIP(f : Object, whole : Object, part : Object)
  requires f.Ready() && whole.Ready() && part.Ready()

 //same as no incomeing pointers but variables somewhat renamed...

  requires strictlyInside(part,whole)
  requires outside(f,whole)
//  requires outside(part,f)

   ensures not(refOK(f,part))
{}


lemma {:isolate_assertions} ShorterNoIncomingPointers(f : Object, o : Object, t : Object)
  requires f.Ready() && o.Ready() && t.Ready()
//  requires f != t

  requires strictlyInside(t,o)
  requires outside(f,o)
  //requires outside(t,f)

   ensures not(refOK(f,t))
{
  assert f != t;

 assert outside(f,t);  assert not(inside(f,t));

   assert refOK(f,t)  ==> ((f==t) || refBI(f,t) || refDI(f,t));
   assert refOK(f,t) <==  ((f==t) || refBI(f,t) || refDI(f,t));
   assert refOK(f,t) <==> ((f==t) || refBI(f,t) || refDI(f,t));

   assert not(f==t);
   assert not(refBI(f,t));

   if (refDI(f,t)) {
     assert f in t.owner;
     DreddOwner(f,t);
      assert inside(t,f);
  //    assert outside(t,f);

//       assert t == f;
//       assert t != f;
//
//      assert false;
   } else {

   assert not(refDI(f,t));
  assert not(refOK(f,t));
   }

assert not(refOK(f,t));
}




lemma {:isolate_assertions} LongerNoIncomingPointers(f : Object, o : Object, t : Object)
  requires f.Ready()
  requires o.Ready()
  requires t.Ready()

  ///all objects are distinct
  //requires f != o
  requires f != t
  //requires o != t

  requires strictlyInside(t,o)
  requires outside(f,o)
//  requires outside(t,f)

   ensures not(refOK(f,t))
{
//
//  assert outside(f,t);  assert not(inside(f,t));
//
// //    assert refOK(f,t)  ==> ((f==t) || refBI(f,t) || refDI(f,t));
// //    assert refOK(f,t) <==  ((f==t) || refBI(f,t) || refDI(f,t));
//    assert refOK(f,t) <==> ((f==t) || refBI(f,t) || refDI(f,t));
//
//    assert not(f==t);
//    assert not(refBI(f,t));

   if (refDI(f,t)) {
      assert f in t.owner;
      DreddOwner(f,t);
    //   assert inside(t,f);
    //   assert outside(t,f);
      assert t == f;
      assert t != f;

      assert false;
   } else {

//    assert not(refDI(f,t));
   assert not(refOK(f,t));
   }

 assert not(refOK(f,t));
}



lemma {:isolate_assertions } fint_refDI_outside(f : Object, t : Object)
  requires f.Ready()
  requires t.Ready()
  requires t.owner == {f}
   ensures refDI_fall(f,t)
   ensures refDI_seqo(f,t)
    // ensures refDI_fint(f,t)
  ensures refDI(f,t)
  ensures refOK(f,t)
  ensures flatten(f.self) == flatten(t.owner)
{
     DreddOwner(f,t);
      assert inside(t,f);
//    assert outside(t,f);
}