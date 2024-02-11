Require Import Nyan.Theory.Category.
Require Import Nyan.Theory.Arr.
Require Import Nyan.Theory.Dual.
Require Import Nyan.Theory.Ism.

Definition Set_arrow_relation (A B : Set) : relation (A -> B).
Proof.
  unfold relation.
  intros f g.
  apply (forall x, f x = g x).
Defined.

Definition Set_arrow_equiv (A B: Set) : Equivalence (Set_arrow_relation A B).
Proof.
  constructor; unfold Reflexive, Symmetric, Transitive, Set_arrow_relation; intros.
  - reflexivity.
  - symmetry. apply H.
  - rewrite H. apply H0.
Defined.

Definition Set_id_left_right: forall (A B : Set) (f : A -> B),
  Set_arrow_relation A B (fun a : A => f a) f.
Proof.
  intros.
  unfold Set_arrow_relation.
  intros. reflexivity.
Defined.

Definition Set_assoc : forall 
  (A B C D : Set) 
    (f : A -> B) 
    (g : B -> C) 
    (h : C -> D),
  Set_arrow_relation A D (fun a : A => h (g (f a))) (fun a : A => h (g (f a))).
Proof.
  unfold Set_arrow_relation.
  intros.
  reflexivity.
Defined.

Definition Set_cat_compose_proper :
forall A B C : Set,
  Proper
    (Set_arrow_relation A B ==>
     Set_arrow_relation B C ==> Set_arrow_relation A C)
    (fun (f : A -> B) (g : B -> C) (a : A) => g (f a)).
Proof.
  unfold Set_arrow_relation, Proper, respectful.
  intros A B C f f' Hf g g' Hg x.
  rewrite Hf, Hg.
  reflexivity.
Defined.

#[export] Instance Category_Set : Category := {
  object := Set;
  arrow  := fun A B => A -> B;
  compose := fun A B C f g a => g (f a);
  arrow_relation := fun A B => Set_arrow_relation A B;
  arrow_equiv := fun A B => Set_arrow_equiv A B;
  cat_compose_proper := Set_cat_compose_proper;
  id := fun A => fun a => a;
  id_left := Set_id_left_right;
  id_right := Set_id_left_right;
  assoc := Set_assoc;
}.

(* Examples of categories of arrows *)
Definition Category_Arr_Set := Category_Arr Category_Set.
Definition Category_Arr2_Set := Category_Arr (Category_Arr Category_Set).

(* The Dual of the Set category *)
Definition Category_Dual_Set := Category_Dual Category_Set.

(* monic and epic *)
Definition injective {A B} (f : A -> B) := forall a1 a2, f a1 = f a2 -> a1 = a2.
Definition surjective {A B} (f : A -> B) := forall b, exists a, f a = b.

Lemma monic_set_inj : forall (B C: Set) (f: B ~> C), 
  monic Category_Set B C f <-> injective f.
Proof.
  unfold "~>", monic, injective. 
  simpl.
  unfold Set_arrow_relation.
  intros B C f.
  split.
  - intros H_monic b1 b2 H_inj.
    specialize H_monic with C (fun _ => b1) (fun _ => b2) (f b1).
    simpl in *.
    apply H_monic.
    intros.
    assumption.
  - intros H_inj A g h H_monic x.
    apply H_inj, H_monic.
Qed.

Lemma epic_set_sur : forall (A B: Set) (f: A ~> B), 
  epic Category_Set A B f <-> surjective f.
Proof.
  unfold "~>", epic, surjective.
  simpl.
  unfold Set_arrow_relation.
  intros A B f.
  split.
  - admit.
  - intros H C g h H' b. 
    specialize H with b.
    destruct H as [a e].
    subst.
    apply H'.
Admitted.
