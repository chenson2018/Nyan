Require Import Nyan.Theory.Category.
Open Scope Cat.

Definition monic {Cat: Category} {B C: object} (f: arrow B C) := 
  forall A (g h: A ~> B), f ∘ g ≈ f ∘ h -> g ≈ h.

Definition epic {Cat: Category} {A B: object} (f: arrow A B) := 
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

  Lemma epic_decompose : epic (g ∘ f) -> epic f.
  Proof.
  Admitted.  

End ism_compose.
