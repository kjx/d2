include "Object.dfy"
include "Ownership.dfy"

///////////////////////////////////////////////////////////////////////////////////
//modes aka "reference capabilities"  YUCK
//
//
//  Modes tacked on the bottom of Object.dfy to avoid circular imports.
//  also this isn't that important right now
//
// //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
// //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//
datatype Mode =
  | Rep // owned by me
  | Peer // owned by my owner
    //For all the Owner & Read "Modes" sholdn't the owner always be "self" i.e; the object containing the reernce.
  | Owned(perm : Perm) //unrestricted, Rust-style owning reference - with no borrows!
  | Loaned(perm : Perm) //owning reference, but currently there are "borrowed" references to it
  | Borrow(perm: Perm, owner: Owner, from : Object, name : string) //borrowed reference, borrowe from that object!
    //when one does a "stack-pop-return" into the obejct that this was borrowed from
    //then the Mode of the owning refernece goes from Loaned -> Owned
  | Self // points to yourself
  | Evil //type dyanmic.  So I don't hace to do the full checks right now --- kjx 7 May 2024


datatype Perm = Read | Write | Local   ///or should these be object kinds???>  ARGH!!

predicate modeOK(f : Object, m : Mode, t : Object)
  //can object o point to object v
  //can object v be assigned to a field of Mode t within object o?
  //NOTE EVIL cutrently ignor4s OWNERSHIP in this definition!!!!!
{
  match m
  case Evil => true
  case Rep | Owned(_) | Loaned(_) => refDI(f,t)
  case Peer => (f.owner == t.owner)
  case Borrow(_,_,_,_) => refOK(f,t)
  case Self => (f == t) // this is apparently redundant, dont' know what
}

lemma MODE_INDIGO(f : Object, m : Mode, t : Object)
    requires m == Evil
     ensures modeOK(f,m,t)
{}

//
lemma MODE_SANITY(m : Mode, o : Object)
  requires m.Self?
   ensures modeOK(o,m,o)
{}
