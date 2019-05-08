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

Notation "x =? y" := (eqb x y) (at level 60).

Section DecidableKeys.
  (**
     In this section, the type K is declared as an instance of EqDec in
     order to be used for the keys of the map.
   *)
  Generalizable Variable K.
  Context `{KDec: EqDec K}.

  (**
     A [mapping] is define as an inductive Type.
     There is a typeclass constraint on K.
   *)
  Inductive mapping `{EqDec K} {E: Type} : Type :=
  | empty : mapping
  | record : K -> E -> mapping -> mapping.

  (**
     The [find] function return an [option] of the type of the elements.
   *)
  Fixpoint find {E:Type} (k1:K) (m:mapping): option E :=
    match m with
    | empty => None
    | record k2 e m' =>
      if k1 =? k2
      then Some e
      else find k1 m'
    end.

  (**
     The [mem] predicate indicates wether there is an occurrence of the 
     given key.
   *)
  Fixpoint mem {E:Type} (k1:K) (m:@mapping KDec E): bool :=
    match m with
    | empty => false
    | record k2 e m' =>
      if  k1 =? k2
      then true
      else mem k1 m'
    end.
  
  (**
     The [remove] function delete all the entries with the given key.
   *)
  Fixpoint remove {E:Type} (k1:K) (m:@mapping KDec E): mapping :=
    match m with
    | empty => empty
    | record k2 e m' =>
      if k1 =? k2
      then remove k1 m'
      else record k2 e (remove k1 m')
    end.

  (**
     The [update] function return the [mapping] updated with the new value 
     at the given key.
     This function guaranties that there is never several occurences of the
     same key in a [mapping].
   *)
  Definition update {E:Type} (k:K) (e:E) (m:mapping): mapping :=
    if mem k m
    then record k e (remove k m)
    else record k e m.

  (**
     The [mapElements] function is map the given function on the elements
     of the [mapping] without changing the keys.
   *)
  Fixpoint mapElements {E1 E2: Type}
           (f: E1 -> E2)
           (m: @mapping KDec E1): @mapping KDec E2 :=
    match m with
    | empty => empty
    | record k e m' => record k (f e) (mapElements f m')
    end.

  

End DecidableKeys.

