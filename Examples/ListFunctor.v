Require Import Nyan.Theory.Category.
Require Import Nyan.Theory.Functor.
Require Import Nyan.Theory.Ism.
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
  - unfold Proper, respectful.
    intros.
    apply map_ext.
    assumption.
Defined.

(* then as a functor from Set to Monoid *)

#[export] Instance List_Monoid (X: Set) : Monoid.
Proof.
  (* this is messy because of the order, I should really learn do do this properly... *)
  apply (Build_Monoid (list X) (@app X) []); intros.
  - apply app_assoc.
  - reflexivity.
  - apply app_nil_r.
Defined.

Definition List_Monoid_arrow {A B: Category_Set.(object)} (f: A ~> B) :
  List_Monoid A ~> List_Monoid B.
Proof.
  simpl in *.
  unfold List_Monoid.
  apply (Build_Monoid_Homomorphism (List_Monoid A) (List_Monoid B) (@map A B f)); simpl.
  - reflexivity.
  - intros. apply map_app.
Defined.

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
  - simpl. intros. apply map_id.
  - unfold List_Monoid_arrow. simpl. intros. symmetry. apply map_map.
  - unfold Proper, respectful.
    simpl in *.
    unfold Set_arrow_relation.
    intros.
    apply map_ext.
    assumption.
Qed.

#[export] Instance Reverse_Natural_Isomorphism : Natural_Isomorphism Functor_maplist Functor_maplist.
Proof.
  unfold Functor_maplist.
  simpl.
  apply Build_Natural_Isomorphism with (fun A : Set => @rev A).
  - simpl. unfold Set_arrow_relation.
    intros A B f xs.
    apply map_rev.
  - simpl.
    intros A. 
    apply Build_Iso with (@rev A)
    ; simpl
    ; unfold Set_arrow_relation
    ; intro xs
    ; apply rev_involutive.
Qed.    
