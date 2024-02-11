Require Import Nyan.Category.
Require Import Nyan.Arr.
Require Import Nyan.Dual.
Require Import Nyan.Ism.

#[export] Instance Category_Set : Category := {
  object := Set;
  arrow  := fun A B => A -> B;
  compose := fun A B C f g a => g (f a);
  arrow_relation := fun _ _ => eq;
  arrow_equiv := fun _ _ => eq_equivalence;
  cat_compose_proper := fun A B C => reflexive_proper (fun (f : A -> B) (g : B -> C) (a : A) => g (f a));
  id := fun A => fun A => A;
  id_left := fun A B f => eq_refl;
  id_right := fun A B f => eq_refl;
  assoc := fun A B C D f g h => eq_refl;
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
Admitted.

Lemma epic_set_sur : forall (A B: Set) (f: Category_Set.(arrow) A B), epic Category_Set A B f <-> surjective f.
Proof.
Admitted.
