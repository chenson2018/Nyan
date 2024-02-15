Require Import Nyan.Theory.Category.
Require Import Nyan.Theory.Ism.
Require Import Nyan.Theory.Product.
Require Import Nyan.Theory.Universal.
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

Notation "g ⊚ f" := (compose_Functor f g) (at level 40, left associativity): category_scope.

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

#[export] Instance Diagonal_Functor (Cat: Category) : Functor Cat (Category_Product Cat Cat) := {
  fmap := fun A => (A, A);
  fmap_arr := fun _ _ f => (f, f);
  functor_id := fun _ => conj (reflexivity _) (reflexivity _);
  functor_compose := fun _ _ _ _ _ => conj (reflexivity _) (reflexivity _);
  fmap_proper := fun _ _ _ _ H => conj H H;
}.

Section prod_func.
  Context (Cat : Category).
  Variable H : forall A B : Cat.(object), Product A B.

  #[export] Program Instance Product_Functor : Functor (Category_Product Cat Cat) Cat := {
    fmap := fun AB => (H (fst AB) (snd AB)).(p_AxB);
  }.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.
End prod_func.

Class Natural_Transformation {C D: Category} (F G : Functor C D) := {
  eta_t (A : C.(object)): F.(fmap) A ~> G.(fmap) A;
  nat_trans_comm {A B} (f : A ~> B) : G.(fmap_arr) f ∘ eta_t A ≈ eta_t B ∘ F.(fmap_arr) f
}.

Class Natural_Isomorphism {C D: Category} (F G : Functor C D) := {
  eta_i (A : C.(object)): F.(fmap) A ~> G.(fmap) A;
  nat_iso_comm {A B} (f : A ~> B) : G.(fmap_arr) f ∘ eta_i A ≈ eta_i B ∘ F.(fmap_arr) f;
  eta_i_iso : forall A, Iso (eta_i A)
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

Class Adjunction {C D: Category} (F: Functor C D) (G: Functor D C) := {
  adjunct_trans : Natural_Transformation (Identity_Functor C) (G ⊚ F);
  adjunct_comm {X}: 
      sigT (fun Y : D.(object)
      => 
      sigT (fun f: X ~> G.(fmap) Y 
      => 
      sigT (fun fsharp : F.(fmap)X ~> Y 
      => 
      f ≈ G.(fmap_arr) fsharp ∘ adjunct_trans.(eta_t) X
      )));
  (* TODO require that the above fsharp is unique *)
}.
