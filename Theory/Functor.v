Require Import Nyan.Theory.Category.
Require Import Nyan.Theory.Ism.
Open Scope Cat.

Section functor.
  Variables C D : Category.

  Class Functor (C D :Category) := {
    fmap : 
      C.(object) -> D.(object);

    fmap_arr {A B} : 
      A ~> B -> fmap A ~> fmap B;

    functor_id {A} : fmap_arr (@id C A) ≈ id;

    functor_compose {A B C} (f: A ~> B) (g: B ~> C):
      fmap_arr (g ∘ f) ≈ fmap_arr g ∘ fmap_arr f;

    fmap_proper {a b: C.(object)} : Proper (@arrow_relation C a b ==> D.(arrow_relation)) fmap_arr;
  }.

End functor.

#[export] Instance Functor_Morphism (C D: Category) (F: Functor C D) (a b: C.(object)):
  Proper (@arrow_relation C a b ==> D.(arrow_relation)) fmap_arr.
Proof. apply fmap_proper. Qed.


Definition fc {A B C : Category} {F: Functor A B} {G: Functor B C} :
    forall a b,    
    a ~> b -> 
    G.(fmap) (F.(fmap) a) ~> G.(fmap) (F.(fmap) b).
Proof.
  intros.
  destruct F as [map_F fmap_arr_F functor_id_F functor_compose_F].
  destruct G as [map_G fmap_arr_G functor_id_G functor_compose_G].
  simpl in *.
  apply fmap_arr_G, fmap_arr_F.
  assumption.
Defined.    

Definition compose_Functor {A B C : Category} (F: Functor A B) (G: Functor B C) : Functor A C.
Proof.
  apply (Build_Functor A C (fun a => G.(fmap) (F.(fmap) a)) fc).
  - intros a. unfold fc. 
    destruct F, G.
    simpl in *.
    rewrite functor_id0, functor_id1.
    reflexivity.
  - intros a b c f g.
    unfold fc.
    destruct F, G.
    simpl in *.
    rewrite functor_compose0, functor_compose1.
    reflexivity.
  - intros. unfold fc.
    destruct F, G.
    unfold Proper, respectful.
    intros ab1 ab2 rel.
    rewrite rel.
    reflexivity.
Defined.      

Notation "g ◯  f" := (compose_Functor f g) (at level 40, left associativity): category_scope.

Class Natural_Transformation {C D: Category} (F G : Functor C D) := {
  eta_t (A : C.(object)): F.(fmap) A ~> G.(fmap) A;
  nat_trans_comm {A B} (f : A ~> B) : G.(fmap_arr) f ∘ eta_t A ≈ eta_t B ∘ F.(fmap_arr) f
}.

Class Natural_Isomorphism {C D: Category} (F G : Functor C D) := {
  eta_i (A : C.(object)): F.(fmap) A ~> G.(fmap) A;
  nat_iso_comm {A B} (f : A ~> B) : G.(fmap_arr) f ∘ eta_i A ≈ eta_i B ∘ F.(fmap_arr) f;
  eta_i_iso : forall A, Iso (eta_i A)
}.
