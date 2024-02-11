Require Import Nyan.Theory.Category.
Open Scope Cat.

Definition relation_pair {X Y: Type} (rX: relation X) (rY: relation Y) : relation (X * Y).
Proof.
  unfold relation.
  intros [x1 y1] [x2 y2].
  apply (rX x1 x2 /\ rY y1 y2).
Defined.     

(* given a category, the category of its arrows *)

Section arrow_cat.
  Context (Cat: Category).

  Definition arrow_arrow (a b: {A & {B & A ~> B}}) : Type.
  Proof.
    destruct a as [A  [B  AtoB  ]].
    destruct b as [A' [B' A'toB']].
    apply ((A ~> A') * (B ~> B'))%type.
  Defined.    

  Notation "f ~~> g"   := 
    (arrow_arrow f g) (at level 90, right associativity): category_scope.

  Definition arrow_arrow_compose :
    forall 
    (a b c: {A & {B & A ~> B}}),
    a ~~> b -> b ~~> c -> a ~~> c.
  Proof. 
    intros [A [B AB]] [A' [B' A'B']] [A'' [B'' A''C'']] ab bc.
    unfold arrow_arrow in *.
    destruct ab as [A_A' B_B'].
    destruct bc as [A'_A'' B'_B''].
    constructor.
    - apply (compose A_A' A'_A'').
    - apply (compose B_B' B'_B'').
  Defined.

  Definition arrow_arrow_relation :
    forall 
    (a b: {A & {B & A ~> B}}),
    relation (a ~~> b).
  Proof.
     intros [A [B AB]] [A' [B' A'B']].
     simpl.
     apply relation_pair; apply arrow_relation.
  Defined.     

  (* this is a bit odd notation, but that's okay... *)
  Notation "f ≈≈ g" := (arrow_arrow_relation f g) (at level 79) : category_scope.

  Definition arrow_arrow_equiv :
    forall 
    (a b: {A & {B & A ~> B}}),
    Equivalence (a ≈≈ b).
  Proof.
    intros [A [B AB]] [A' [B' A'B']].
    simpl.
    constructor.
    - unfold Reflexive. intros [A_A' B_B']. simpl. split; reflexivity.
    - unfold Symmetric. intros [A_A'_1 B_B'_1] [A_A'_2 B_B'_2] [rel_a rel_b]. simpl.
      split; symmetry; assumption.
    - unfold Transitive.
      intros [A_A'_1 B_B'_1] [A_A'_2 B_B'_2] [A_A'_3 B_B'_3].
      simpl.
      intros [a_1_2 b_1_2] [a_2_3 b_2_3].
      split.
      + rewrite a_1_2. assumption.
      + rewrite b_1_2. assumption.
  Defined.
     
  Definition arrow_arrow_cat_compose_proper :
    forall 
      (a b c: {A & {B & A ~> B}}),
      Proper ((a ≈≈ b) ==> (b ≈≈ c) ==> (a ≈≈ c)) (arrow_arrow_compose a b c).
  Proof.
     intros [A [B AB]] [A' [B' A'B']] [A'' [B'' A''C'']].
     simpl.
     unfold Proper, respectful.
     intros [A_A'_1 B_B'_1] [A_A'_2 B_B'_2].
     simpl.
     intros [rel_a_1 rel_b_1] [A'_A''_1 B'_B''_1] [A'_A''_2 B'_B''_2] [rel_a_2 rel_b_2].
     simpl.
     constructor.
     - rewrite rel_a_1, rel_a_2. reflexivity.
     - rewrite rel_b_1, rel_b_2. reflexivity.
  Defined.

  Definition arrow_arrow_id : forall (a: {A & {B & A ~> B}}), a ~~> a.
  Proof. 
    intros [A [B AB]].
    simpl. constructor; apply id.
  Defined.    

  Definition arrow_arrow_id_left : forall 
    (a b: {A & {B & A ~> B}})
    (f : a ~~> b), 
    arrow_arrow_relation a b
      (arrow_arrow_compose a b b f (arrow_arrow_id b))
      f.
  Proof.
     intros [A [B AB]] [A' [B' A'B']].
     simpl.
     intros [A_A' B_B'].
     simpl.
     constructor; apply id_left.
  Defined.

  Definition arrow_arrow_id_right : forall 
    (a b: {A & {B & arrow A B}})
    (f : arrow_arrow a b),
      arrow_arrow_relation a b
        (arrow_arrow_compose a a b (arrow_arrow_id a) f)
        f.
  Proof.
     intros [A [B AB]] [A' [B' A'B']].
     simpl.
     intros [A_A' B_B'].
     simpl.
     constructor; apply id_right.
  Defined.     
  
  Definition arrow_arrow_assoc : forall 
    (a b c d: {A & {B & A ~> B}})
    (f : a ~~> b) 
    (g : b ~~> c) 
    (h : c ~~> d), 
    arrow_arrow_relation a d
     (arrow_arrow_compose a c d (arrow_arrow_compose a b c f g) h)
     (arrow_arrow_compose a b d f (arrow_arrow_compose b c d g h)).
  Proof.
     intros [A [B AB]] [A' [B' A'B']] [A'' [B'' A''C'']] [A''' [B''' A'''C''']].
     simpl.
     intros [A_A' B_B'] [A'_A'' B'_B''] [A''_A''' B''_B'''].
     simpl.
     constructor; apply assoc.
  Defined.    

  #[export] Instance Category_Arr : Category := {
    object := sigT (fun A => sigT (fun B => arrow A B));
    arrow  := fun a b => a ~~> b; 
    compose := arrow_arrow_compose;
    arrow_relation := arrow_arrow_relation;
    arrow_equiv := arrow_arrow_equiv;
    cat_compose_proper := arrow_arrow_cat_compose_proper ;
    id := arrow_arrow_id;
    id_left := arrow_arrow_id_left;
    id_right := arrow_arrow_id_right;
    assoc := arrow_arrow_assoc;
  }.

End arrow_cat.
