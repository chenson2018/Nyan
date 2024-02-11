Require Import Nyan.Theory.Category.

Class Poset : Type := {
    poset_X      : Type;
    poset_leq    : poset_X -> poset_X -> Prop;
    poset_refl   : forall x     : poset_X, poset_leq x x;
    poset_antisym: forall x y   : poset_X, poset_leq x y -> poset_leq y x -> x = y;
    poset_trans  : forall x y z : poset_X, poset_leq x y -> poset_leq y z -> poset_leq x z;
}.

Class Poset_Preserving (P: Poset) (Q: Poset) := {
  poset_map : P.(poset_X) -> Q.(poset_X);
  preserve  : forall p p', P.(poset_leq) p p' -> Q.(poset_leq) (poset_map p) (poset_map p');
}.

Definition Poset_compose : forall A B C : 
  Poset, Poset_Preserving A B -> Poset_Preserving B C -> Poset_Preserving A C.
Proof.
  intros A B C morphAB morphBC.
  destruct morphAB as [fAB preAB].
  destruct morphBC as [fBC preBC].
  apply (Build_Poset_Preserving _ _ (fun a => fBC (fAB a))).
  intros.
  apply preBC, preAB.
  assumption.
Defined.

Definition Poset_Preserving_relation (A B : Poset) (f g : Poset_Preserving A B) := f.(poset_map) = g.(poset_map).

Lemma Poset_Preserving_Equivalence : forall A B : Poset, Equivalence (Poset_Preserving_relation A B).
Proof.
  intros.
  constructor.
  - unfold Reflexive. reflexivity.
  - unfold Symmetric. intros. symmetry. assumption.
  - unfold Transitive, Poset_Preserving_relation. intros. rewrite H. assumption.
Qed.    

Lemma Poset_cat_compose_proper :
  forall A B C : Poset,
    Proper
      (Poset_Preserving_relation A B ==>
       Poset_Preserving_relation B C ==> 
       Poset_Preserving_relation A C)
      (Poset_compose A B C).
Proof.
  intros. 
  unfold Proper, respectful.
  intros.
  unfold Poset_Preserving_relation.
  unfold Poset_compose.
  destruct x, x0, y, y0.
  simpl.
  unfold Poset_Preserving_relation in *.
  simpl in H0, H.
  subst.
  reflexivity.
Qed.  

Definition Poset_id : forall A : Poset, Poset_Preserving A A.
Proof.
  intros.
  apply (Build_Poset_Preserving _ _ (fun a => a)).
  intros. assumption.
Defined.

Lemma Poset_id_left : forall (A B : Poset) (f : Poset_Preserving A B),
  Poset_Preserving_relation A B (Poset_compose A B B f (Poset_id B)) f.
Proof.
  intros.
  unfold Poset_Preserving_relation.
  destruct f.
  simpl.
  reflexivity.
Qed.

Lemma Poset_id_right: forall (A B : Poset) (f : Poset_Preserving A B),
  Poset_Preserving_relation A B (Poset_compose A A B (Poset_id A) f) f.
Proof.
  intros.
  unfold Poset_Preserving_relation.
  destruct f.
  simpl.
  reflexivity.
Qed.  

Lemma Poset_assoc : forall (A B C D : Poset) (f : Poset_Preserving A B)
    (g : Poset_Preserving B C) (h : Poset_Preserving C D),
  Poset_Preserving_relation A D
    (Poset_compose A C D (Poset_compose A B C f g) h)
    (Poset_compose A B D f (Poset_compose B C D g h)).
Proof.
  intros.
  unfold Poset_Preserving_relation.
  destruct f, g, h.
  simpl.
  reflexivity.
Qed.  

#[export] Instance Category_Poset : Category := {
  object  := Poset;
  arrow   := Poset_Preserving;
  compose := Poset_compose;
  arrow_relation := Poset_Preserving_relation;
  arrow_equiv := Poset_Preserving_Equivalence;
  cat_compose_proper := Poset_cat_compose_proper;
  id := Poset_id;
  id_left  := Poset_id_left;
  id_right := Poset_id_right;
  assoc    := Poset_assoc;
}.

Section category_poset_induced.
  Context (P: Poset).

  (* is this a good notion of poset equality? *)
  Definition Poset_relation_induced : forall A B : poset_X, relation (poset_leq A B) := 
    fun A B => (fun X Y => poset_leq A B).
    
  Lemma Poset_relation_induced_Equivalence : forall A B : P.(poset_X), Equivalence (Poset_relation_induced A B).
  Proof.
    intros. 
      constructor
    ; unfold Reflexive, Symmetric, Transitive, Poset_relation_induced
    ; intros
    ; assumption.
  Qed.

  Lemma Poset_relation_induced_proper : 
    forall A B C : poset_X,
      Proper
        (Poset_relation_induced A B ==>
         Poset_relation_induced B C ==> Poset_relation_induced A C)
        (poset_trans A B C).
  Proof.
    intros.
    unfold Proper, respectful, Poset_relation_induced.
    intros.
    apply (poset_trans A B C H H0).
  Qed.    

  Lemma Poset_induced_assoc : forall (A B C D : poset_X) (f : poset_leq A B)
    (g : poset_leq B C) (h : poset_leq C D),
  Poset_relation_induced A D
    (poset_trans A C D (poset_trans A B C f g) h)
    (poset_trans A B D f (poset_trans B C D g h)).
  Proof.
    unfold Poset_relation_induced.
    intros.
    assert (poset_leq A C).
    { apply (poset_trans A B C f g). }
    apply (poset_trans A C D H h).
  Qed.

  (* note mixing of left/right *)
  #[export] Instance Category_Poset_Induced : Category :=
    {
      object := poset_X;
      arrow := poset_leq;
      compose := poset_trans;
      arrow_relation := Poset_relation_induced;
      arrow_equiv    := Poset_relation_induced_Equivalence;
      cat_compose_proper := Poset_relation_induced_proper;
      id := poset_refl;
      id_left := fun _ _ f => f;
      id_right := fun _ _ f => f;
      assoc := Poset_induced_assoc;
    }.

End category_poset_induced.

Require Import Arith.

#[local] Instance Nat_le_Poset : Poset := {
  poset_X       := nat;
  poset_leq     := le;
  poset_refl    := Nat.le_refl;
  poset_antisym := Nat.le_antisymm;
  poset_trans   := Nat.le_trans;
}.

Definition Nat_le_Poset_Cat := Category_Poset_Induced Nat_le_Poset.

(* all arrows coorespond to <= *)
Lemma arrow_implies_le : forall x y,  Nat_le_Poset_Cat.(arrow) x y -> x <= y.
Proof. simpl. intros. assumption. Qed.

Lemma le_implies_arrow : forall x y,  x <= y -> Nat_le_Poset_Cat.(arrow) x y.
Proof. simpl. intros. assumption. Qed.
