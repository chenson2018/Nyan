Require Import Nyan.Theory.Category.
Open Scope Cat.

(* 
   The object names are chosen to evoke the imagery of (A | A') ~> B ~> (C | C')
    - monic forces the left arrows to be the same
    - epic forces the right arrows to be the same
*)

Definition monic {Cat: Category} {B C: object} (f: B ~> C) := 
  forall A (g h: A ~> B), f ∘ g ≈ f ∘ h -> g ≈ h.

Definition epic {Cat: Category} {A B: object} (f: A ~> B) := 
  forall C (g h : B ~> C), g ∘ f ≈ h ∘ f -> g ≈ h.

Section ism_compose.

  Context (Cat: Category).
  Variables A B C: object.
  Variable f: A ~> B.
  Variable g: B ~> C.

  Lemma monic_compose : monic f -> monic g -> monic (g ∘ f).
  Proof.
    unfold monic.
    intros Hf Hg pre_A f' g' comp.
    apply Hf, Hg.
    repeat rewrite assoc.
    assumption.
  Qed.

  Lemma monic_decompose : monic (g ∘ f) -> monic f.
  Proof.
    unfold monic.
    intros monic_comp pre_A f' g' H.
    apply monic_comp.
    repeat rewrite <- assoc.
    rewrite H.
    reflexivity.
  Qed.

  Lemma epic_compose : epic f -> epic g -> epic (g ∘ f).
  Proof.
    unfold epic.
    intros Hf Hg post_C f' g' comp.
    apply Hg, Hf.
    repeat rewrite <- assoc.
    assumption.
  Qed.

  Lemma epic_decompose : epic (g ∘ f) -> epic g.
  Proof.
    unfold epic.
    intros comp_epic.
    intros O g' h' H.
    apply comp_epic.
    repeat rewrite assoc.
    rewrite H.
    reflexivity.
  Qed.
    
End ism_compose.

(* making this a class makes cetain statements easier *)
Class Iso {Cat: Category} {A B: object} (f: A ~> B) := {
  iso_inv  : B ~> A;
  iso_left : iso_inv ∘ f ≈ id;
  iso_right: f ∘ iso_inv ≈ id;
}.

Section iso_properties.
  Context (Cat: Category).
  Variables A B C: object.
  Variable f: A ~> B.

  Lemma iso_unique (I I': Iso f): I.(iso_inv) ≈ I'.(iso_inv).
  Proof.
    destruct I as [h h_left h_right].
    destruct I' as [g g_left g_right].
    simpl.
    rewrite <- (id_right h).
    rewrite <- (id_left g).
    rewrite <- g_right.
    rewrite <- h_left.
    apply assoc.
  Qed.

  Variable g: B ~> C.

  Lemma inv_compose : Iso f -> Iso g -> Iso (g ∘ f).
  Proof.
    intros [finv f_left f_right] [ginv g_left g_right].
    apply Build_Iso with (finv ∘ ginv).
    - rewrite <- assoc.
      rewrite (assoc _ _ ginv). 
      rewrite g_left.
      rewrite id_left.
      assumption.
    - rewrite <- assoc.
      rewrite (assoc _ finv _). 
      rewrite f_right.
      rewrite id_left.
      assumption.
  Qed.
End iso_properties.
