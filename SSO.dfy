include "Klon.dfy"

///NOTE - swapped HighCalidFragilistic(m) for m.SuperCalidFragilistic()
//so we didn't nneed to import highLIine

//sso content from old M2.dfy
//note good stuff moved into H2.dfy

include "Ownership-Lemmata.dfy"
include "Ownership-Recursive.dfy"
include "Printing.dfy"


// =================================================


type SSO = set<set<Object>>

function      ownr2sso(o : OWNR) : SSO                           { set x : Object <- o :: x.AMFO }
function obj2sso(o : Object) : SSO      requires o.Ready()  { ownr2sso(o.AMFO) } // requires o.Ready() ?
function concensso(sso : SSO) : OWNR { set so : set<Object> <- sso, o : Object <- so :: o }

predicate old_allinsso(oo : SSO, p : SSO) { forall o <- oo :: o > concensso(p) }
predicate allinsso(oo : SSO, p : SSO) { forall o <- oo :: o > concensso(p) }


predicate fromsso(oo : SSO, p : SSO)  { concensso(oo) > concensso(p) }  //not that usefull








  function {:isolate_assertions} {:timeLimit 20} mapfo(oo : OWNR, m : Klon) : SSO
   requires forall o <- oo :: m.objectReadyInKlown(o)
   requires oo <= m.m.Keys
   requires m.SuperCalidFragilistic()
    ensures                 m.o.AMFO <= m.m.Keys
    ensures forall o <- oo :: o.AMFO <= m.m.Keys
   reads oo, m.m.Keys, m.m.Values, m.oHeap
 {
   if ((set o <- oo | inside(o, m.o)) == {})
      then ownr2sso(oo)
      else (mapfo_INNER(oo,m) + obj2sso(m.m[m.o]))
 }

 function {:isolate_assertions} mapfo_INNER_NEW(oo : OWNR, m : Klon) : SSO
   requires forall o <- oo :: m.objectReadyInKlown(o)
   requires oo <= m.m.Keys
   requires m.SuperCalidFragilistic()
      reads oo, m.m.Keys, m.m.Values, m.oHeap
   {
     set y : Object <- (oo - m.o.AMFO) ::
       if (y.AMFO >= m.o.AMFO) then (
            mapfo_SIDEWAYS(y, m)
        ) else ( y.AMFO )
   }


 function {:isolate_assertions} mapfo_INNER(oo : OWNR, m : Klon) : SSO
   requires forall o <- oo :: m.objectReadyInKlown(o)
   requires oo <= m.m.Keys
   requires m.SuperCalidFragilistic()
      reads oo, m.m.Keys, m.m.Values, m.oHeap
   {
//     set y <- (oo - m.o.AMFO) ::
       set y : Object <- (oo - {m.o}) ::
       if (y.AMFO >= m.o.AMFO) then (
        mapThruKlon( (y.AMFO - m.o.AMFO), m ) +  ( m.m[m.o].AMFO )
        ) else ( y.AMFO )
   }

 function {:isolate_assertions}  mapfo_SIDEWAYS(o : Object, m : Klon) : OWNR
   requires m.objectReadyInKlown(o)
   requires o in m.m.Keys
   requires m.SuperCalidFragilistic()
   requires o !in m.o.AMFO
   requires inside(o, m.o)
      reads o, m.m.Keys, m.m.Values, m.oHeap
  { mapThruKlon( (o.AMFO - m.o.AMFO), m ) +  ( m.m[m.o].AMFO ) }



 function {:isolate_assertions} mapfoSide(kk : Owner, m : Klon) : Owner
   requires AllReady(kk)
   requires kk <= m.m.Keys
   requires m.SuperCalidFragilistic()
   requires kk >= m.o.AMFO
      reads kk, m.m.Keys, m.m.Values, m.oHeap
  { mapThruKlon( (kk - m.o.AMFO), m ) +  ( m.m[m.o].AMFO ) }










function sso2setstr(sso: SSO) : set<string>  reads concensso(sso)`nick  { set so <- sso :: "‹"+fmtnickset(so)+"›" }

function  fmtsso(sso: SSO) : string reads concensso(sso)`nick { fmtsetstr(sso2setstr(sso)) }
function ffmtsso(sso: SSO) : string reads concensso(sso)`nick { "«"+fmtsetstr(sso2setstr(sso))+"»" }




function fmtamfosso(y : Object) : string reads y`nick, y.AMFO`nick, concensso(ownr2sso(y.AMFO))`nick  { y.nick + "  " + fmtownrsso(y.AMFO) }

function fmtownrsso(y_AMFO : OWNR) : string reads y_AMFO`nick, concensso(ownr2sso(y_AMFO))`nick { "AMFO=‹" + fmtnickset(y_AMFO) + "›  sso=«" + fmtsso(ownr2sso(y_AMFO)) + "»" }


method printobjectamfoset(s : set<Object>)
{
  var t := s;
  while t != {}
    decreases t
  {
    var y: Object;
    assume exists y : Object <- t ::  forall z : Object <- t :: strLEQ(y.nick, z.nick);
    y :| y in t &&  forall z : Object <- t :: strLEQ(y.nick, z.nick);
//    print y.nick, "     AMFO=‹", fmtnickset(y.AMFO), "›  sso=«", fmtsetstr(sso2setstr(ownr2sso(y.AMFO)))  ,"»\n";
    print fmtamfosso(y), "\n";
    t := t - {y};
  }
}
