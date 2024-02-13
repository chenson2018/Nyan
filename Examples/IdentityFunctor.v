Require Import Nyan.Theory.Category.
Require Import Nyan.Theory.Functor.
Require Import Nyan.Theory.Ism.
Open Scope Cat.

Lemma Identity_Functor_Proper {Cat: Category} : forall a b : object,
  Proper (arrow_relation ==> arrow_relation) (fun f : a ~> b => f).
Proof.
  intros.
  unfold Proper, respectful.
  intros.
  assumption.
Defined.

#[export] Instance Identity_Functor (Cat: Category) : Functor Cat Cat := {
  fmap := fun A => A;
  fmap_arr:= fun _ _ f => f;
  functor_id:= fun _ => reflexivity id;
  functor_compose:= fun _ _ _ _ _ => reflexivity _;
  fmap_proper:= Identity_Functor_Proper;
}.

#[export] Instance Identity_Natural_Isomorphism (Cat: Category) : 
  Natural_Isomorphism (Identity_Functor Cat) (Identity_Functor Cat).
Proof.
  apply Build_Natural_Isomorphism with (fun _ => id).
  - intros. simpl.
    rewrite id_left, id_right.
    reflexivity.
  - intros.
    apply (Build_Iso Cat A A id id)
    ; rewrite id_left
    ; reflexivity.
Qed.

