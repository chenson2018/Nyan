Require Import Nyan.Theory.Category.
Require Import Nyan.Theory.Functor.
Require Import Nyan.Examples.Set.
Require Import Nyan.Examples.Monoid.
Require Import List.
Import ListNotations.

Open Scope Cat.

(* first as a functor from Set to Set *)

#[export] Instance Functor_maplist : 
  Functor Category_Set Category_Set.
Proof.
  apply (Build_Functor Category_Set Category_Set list map)
  ; simpl
  ; unfold Set_arrow_relation
  ; intros.
  - apply map_id.
  - symmetry. apply map_map.
Defined.

(* then as a functor from Set to Monoid *)

#[export] Instance List_Monoid (X: Set) : Monoid.
Proof.
  (* this is messy because of the order, I should really learn do do this properly... *)
  apply (Build_Monoid (list X) (@app X) []); intros.
  - apply app_assoc.
  - reflexivity.
  - apply app_nil_r.
Qed.

(* having trouble with typeclass constructors here... *)

Definition List_Monoid_arrow {A B: Category_Set.(object)} (f: A ~> B) :
  List_Monoid A ~> List_Monoid B.
Proof.
Admitted.

#[export] Instance Functor_maplist_monoid: 
  Functor Category_Set Category_Monoid.
Proof.
  unfold Category_Set, Category_Monoid.
  simpl.
  apply (Build_Functor 
          Category_Set 
          Category_Monoid 
          (fun S => List_Monoid S)
          (fun A B f => List_Monoid_arrow f)
         ).
  - admit.
  - admit.
Admitted.
