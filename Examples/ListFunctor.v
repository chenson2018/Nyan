Require Import Nyan.Theory.Category.
Require Import Nyan.Theory.Functor.
Require Import Nyan.Theory.Ism.
Require Import Nyan.Examples.Set.
Require Import Nyan.Examples.Monoid.
Require Import List.
Import ListNotations.

Open Scope Cat.

(* first as a functor from Set to Set *)

#[export] Instance Functor_List : 
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

#[export] Instance Functor_List_Monoid: 
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
Defined.

#[export] Instance Reverse_Natural_Isomorphism : Natural_Isomorphism Functor_List Functor_List.
Proof.
  unfold Functor_List.
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

(* List.length as an adjunction *)

(* the functor from Mon to Set that forgets the monoid structure *)

#[export] Instance Forgetful_Monoid : Functor Category_Monoid Category_Set.
Proof.
  apply (Build_Functor Category_Monoid Category_Set (fun M => M.(monoid_X)) (fun _ _ f => f.(monoid_homo_f)))
  ; intros
  ; simpl
  ; unfold Set_arrow_relation
  ; intros.
  - reflexivity.
  - destruct f, g. reflexivity.
  - unfold Proper, respectful. intros.
    destruct x, y.
    simpl in *. easy.
Defined.    

(* the natural transformation of singleton lists *)

#[export] Instance Natural_Transformation_Singleton : Natural_Transformation
  (Identity_Functor Category_Set)
  (Forgetful_Monoid ⊚ Functor_List_Monoid).
Proof.
  apply Build_Natural_Transformation with (fun (X : Set) (x : X) => [x]).
  simpl.
  unfold Set_arrow_relation.
  intros. reflexivity.
Defined.

(* length, as a monoid homomorphism from the list monoid to (N,+,0) *)

#[export] Instance Monoid_Homomorphism_Length (X: Set) : Monoid_Homomorphism (List_Monoid X) Monoid_N_Plus.
Proof.
  apply Build_Monoid_Homomorphism with (@length X).
  - reflexivity.
  - simpl. apply app_length.
Defined.    

#[export] Instance Adjunction_List_Length : Adjunction Functor_List_Monoid Forgetful_Monoid.
Proof.
  apply Build_Adjunction with Natural_Transformation_Singleton.
  intros.
  exists Monoid_N_Plus.
  exists (fun _ => 1).
  exists (Monoid_Homomorphism_Length X).
  simpl.
  unfold Set_arrow_relation.
  intros. reflexivity.
Defined.
