Require Import Nyan.Category.
Open Scope Cat.

Section monic.
  Context (Cat: Category).
  Variables B C: object.
  Variable f : arrow B C.
  Definition monic := forall A (g h: A ~> B), f ∘ g ≈ f ∘ h -> g ≈ h.
End monic.

Section epic.
  Context (Cat: Category).
  Variables A B: object.
  Variable f : arrow A B.
  Definition epic := forall C (g h : B ~> C), g ∘ f ≈ h ∘ f -> g ≈ h.
End epic.
