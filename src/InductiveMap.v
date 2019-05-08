Require Import ssreflect ssrbool.
Require Import Notations.


(**
   Define a type class for decidable equality.
*)
Class EqDec (A:Type) :=
  {
    eqb : A -> A -> bool;
    eqb_leibniz : forall x y, eqb x y <-> x = y
    }.

Section DecidableKeys.
  (**
     In this section, the type K is declared as an instance of EqDec in
     order to be used for the keys of the map.
   *)
  Generalizable Variable K.
  Context `{KDec: EqDec K}.

  

End DecidableKeys.

