Require Import Nyan.Theory.Category.

Class Monoid : Type := {
  monoid_X        : Set;
  monoid_op       : monoid_X -> monoid_X -> monoid_X;
  monoid_id       : monoid_X;
  monoid_assoc    : forall x y z, monoid_op x (monoid_op y z) = monoid_op (monoid_op x y) z;
  monoid_id_left  : forall x, monoid_op monoid_id x = x;
  monoid_id_right : forall x, monoid_op x monoid_id = x;
}.

Class Monoid_Homomorphism (M: Monoid) (M' : Monoid) := {
  monoid_homo_f   : M.(monoid_X) -> M'.(monoid_X);
  monoid_homo_e   : monoid_homo_f M.(monoid_id) = M'.(monoid_id);
  monoid_homo_pre : forall x y, monoid_homo_f (M.(monoid_op) x y) = M'.(monoid_op) (monoid_homo_f x) (monoid_homo_f y)
}.

Definition Monoid_compose : forall A B C : 
  Monoid, Monoid_Homomorphism A B -> Monoid_Homomorphism B C -> Monoid_Homomorphism A C.
Proof.
  intros A B C morphAB morphBC.
  destruct morphAB as [fAB preAB].
  destruct morphBC as [fBC preBC].
  apply (Build_Monoid_Homomorphism _ _ (fun a => fBC (fAB a))).
  - rewrite preAB, preBC. reflexivity.
  - intros. rewrite monoid_homo_pre0, monoid_homo_pre1. reflexivity.
Defined.    

Definition Monoid_Homomorphism_relation (A B : Monoid) : 
  (relation (Monoid_Homomorphism A B)).
Proof.
  unfold relation.
  intros f g.
  destruct f, g.
  apply (forall x, monoid_homo_f0 x = monoid_homo_f1 x).
Defined.

Lemma Monoid_Homomorphism_Equivalence : forall A B : Monoid, Equivalence (Monoid_Homomorphism_relation A B).
Proof.
  intros.
  constructor
  ; unfold Reflexive, Symmetric, Transitive, Monoid_Homomorphism_relation
  ; intros
  ; try destruct x
  ; try destruct y
  ; try destruct z
  ; intros
  .
  - reflexivity.
  - symmetry. apply H.
  - rewrite H. apply H0.
Defined.

Lemma Monoid_cat_compose_proper :
  forall A B C : Monoid,
    Proper
      (Monoid_Homomorphism_relation A B ==>
       Monoid_Homomorphism_relation B C ==> 
       Monoid_Homomorphism_relation A C)
      (Monoid_compose A B C).
Proof.
  intros. 
  unfold Proper, respectful.
  intros.
  unfold Monoid_Homomorphism_relation.
  unfold Monoid_compose.
  destruct x, x0, y, y0.
  simpl.
  unfold Monoid_Homomorphism_relation in *.
  simpl in H0, H.
  subst.
  intros.
  rewrite H0, H. reflexivity.
Qed.  

Definition Monoid_id : forall A : Monoid, Monoid_Homomorphism A A.
Proof.
  intros.
  apply (Build_Monoid_Homomorphism _ _ (fun a => a)).
  - reflexivity.
  - intros. reflexivity.
Defined.

Lemma Monoid_id_left : forall (A B : Monoid) (f : Monoid_Homomorphism A B),
  Monoid_Homomorphism_relation A B (Monoid_compose A B B f (Monoid_id B)) f.
Proof.
  intros.
  unfold Monoid_Homomorphism_relation.
  destruct f.
  simpl.
  reflexivity.
Qed.

Lemma Monoid_id_right: forall (A B : Monoid) (f : Monoid_Homomorphism A B),
  Monoid_Homomorphism_relation A B (Monoid_compose A A B (Monoid_id A) f) f.
Proof.
  intros.
  unfold Monoid_Homomorphism_relation.
  destruct f.
  simpl.
  reflexivity.
Qed.  

Lemma Monoid_assoc : forall (A B C D : Monoid) (f : Monoid_Homomorphism A B)
    (g : Monoid_Homomorphism B C) (h : Monoid_Homomorphism C D),
  Monoid_Homomorphism_relation A D
    (Monoid_compose A C D (Monoid_compose A B C f g) h)
    (Monoid_compose A B D f (Monoid_compose B C D g h)).
Proof.
  intros.
  unfold Monoid_Homomorphism_relation.
  destruct f, g, h.
  simpl.
  reflexivity.
Qed.  

(* the category of monoids *)
#[export] Instance Category_Monoid : Category := {
  object  := Monoid;
  arrow   := Monoid_Homomorphism;
  compose := Monoid_compose;
  arrow_relation := Monoid_Homomorphism_relation;
  arrow_equiv := Monoid_Homomorphism_Equivalence;
  cat_compose_proper := Monoid_cat_compose_proper;
  id := Monoid_id;
  id_left  := Monoid_id_left;
  id_right := Monoid_id_right;
  assoc    := Monoid_assoc;
}.

(* a category induced by a particuliar monoid *)
Section category_monoid_induced.
  (* Context makes the typeclasses fields specific to this M *)
  Context (M : Monoid).

  (* note mixing of left/right *)
  #[export] Instance Category_Monoid_Induced : Category :=
    {
      object := unit;
      arrow := fun _ _ => monoid_X;
      compose := fun _ _ _ => monoid_op;
      id := fun a => monoid_id;
      assoc := fun _ _ _ _ f g h => eq_sym (monoid_assoc f g h);
      id_left := fun _ _ f => monoid_id_right f;
      id_right := fun _ _ f => monoid_id_left f;
    }.

End category_monoid_induced.

(* Example of epic/monic not just being surjection/injection *)

Require Import Arith.
Require Import Nyan.Theory.Ism.

#[local] Instance Monoid_N_Plus : Monoid := {
  monoid_X  := nat;
  monoid_op := plus;
  monoid_assoc := Nat.add_assoc;
  monoid_id := 0;
  monoid_id_left := Nat.add_0_l;
  monoid_id_right := Nat.add_0_r;
}.

Require Import ZArith.
Require Import Lia.

#[local] Instance Monoid_Z_Plus : Monoid := {
  monoid_X  := Z;
  monoid_op := Zplus;
  monoid_assoc := Z.add_assoc;
  monoid_id := 0;
  monoid_id_left := Z.add_0_l;
  monoid_id_right := Z.add_0_r;
}.

Lemma N_Z_monoid_homo_pre : forall x y, Z.of_nat (x + y) = Zplus (Z.of_nat x) (Z.of_nat y).
Proof. intros. lia. Qed.

#[local] Instance Inclusion_N_Z : Monoid_Homomorphism Monoid_N_Plus Monoid_Z_Plus := {
  monoid_homo_f   := Z.of_nat;
  monoid_homo_e   := eq_refl;
  monoid_homo_pre := N_Z_monoid_homo_pre;
}.

Lemma Inclusion_N_Z_monic : monic Inclusion_N_Z.
Proof.
  unfold monic. simpl.
  intros A g h H.
  unfold Monoid_Homomorphism_relation in *.
  destruct g, h.
  simpl in *.
  intros x.
  specialize H with x.
  apply Nat2Z.inj in H. assumption.
Qed.

Lemma Inclusion_N_Z_epic : epic Inclusion_N_Z.
Proof.
  unfold epic. simpl.
  intros C g h.
  unfold Monoid_Homomorphism_relation in *.
  destruct g, h.
  simpl in *.
  intros H z.
  destruct C.
  simpl in *.
  destruct (0 <=? z)%Z eqn:bound.
  - apply Zle_bool_imp_le in bound.
    specialize H with (Z.to_nat z).
    rewrite Z2Nat.id in H; assumption.
  - rename monoid_homo_f0 into f.
    rename monoid_homo_f1 into g.
    rename monoid_op0 into f_op.
    rename monoid_id0 into E.
    replace (f z) with (f_op (f z) E) by (apply monoid_id_right0).
    rewrite <- monoid_homo_e1.
    replace 0%Z with (- z + z)%Z by lia.
    rewrite monoid_homo_pre1.
    rewrite monoid_assoc0.
    replace (g (- z)%Z) with (f ((- z))%Z).
    + rewrite <- monoid_homo_pre0.
      replace ((z + - z)%Z) with 0%Z by lia.
      rewrite monoid_homo_e0.
      apply monoid_id_left0.
    + assert (0 <= - z)%Z as neg_z_pos by lia.
      rewrite <- (Z2Nat.id (- z) neg_z_pos) at 1.
      rewrite H.
      rewrite (Z2Nat.id _ neg_z_pos).
      reflexivity.
Qed.
