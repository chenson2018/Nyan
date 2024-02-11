Require Import Nyan.Theory.Category. 
Open Scope Cat.

Section product_cat.
  Variables Q W: Category.

  Definition product_arrow : Q.(object) * W.(object) -> Q.(object) * W.(object) -> Type.
  Proof.
    intros [f_A g_A] [f_B g_B].
    apply ((arrow f_A f_B) * (arrow g_A g_B))%type.
  Defined.
  
  Definition product_compose : 
    forall a b c : Q.(object) * W.(object),
    product_arrow a b -> product_arrow b c -> product_arrow a c.
  Proof.
    intros [A A'] [B B'] [C C'] [AB A'B'] [BC B'C'].
    unfold product_arrow.
    constructor.
    - apply (compose AB BC).
    - apply (compose A'B' B'C').
  Defined.
  
  Definition product_arrow_relation  : 
    forall a b : Q.(object) * W.(object),
    relation (product_arrow a b).
  Proof.
    intros [A A'] [B B'].
    unfold relation.
    simpl.
    intros [AB_1 A'B'_1] [AB_2 A'B'_2].
    apply (AB_1 ≈ AB_2 /\ A'B'_1 ≈ A'B'_2).
  Defined.
  
  Definition product_arrow_equiv :
    forall a b : Q.(object) * W.(object), Equivalence (product_arrow_relation a b).
  Proof.
    intros [A A'] [B B'].
    constructor
    ; unfold Reflexive, Symmetric, Transitive
    ; intros
    ; try destruct x
    ; try destruct y
    ; try destruct z
    ; try destruct H
    ; try destruct H0
    ; simpl
    .
    - split; reflexivity.
    - split; symmetry; assumption.
    - split.
      + rewrite H ,H0. reflexivity.
      + rewrite  H1, H2. reflexivity.
  Defined.
   
  Definition product_cat_compose_proper :
    forall A B C : object * object,
      Proper
        (product_arrow_relation A B ==>
         product_arrow_relation B C ==> product_arrow_relation A C)
        (product_compose A B C).
  Proof.
    intros [A A'] [B B'] [C C'].
    unfold Proper, respectful.
    intros 
      [AB_1 A'B'_1] 
      [AB_2 A'B'_2] 
      [rel_1 rel_1'] 
      [rel_2 rel_2'] 
      [BC B'C']
      [rel_BC rel_B'C'].
      simpl in *.
      split; apply cat_compose_proper; assumption.
  Defined.

  Definition product_id : forall A : Q.(object) * W.(object), product_arrow A A.
  Proof.
    intros [A A'].
    simpl.
    constructor; apply id.
  Defined.

  Definition product_id_left :
    forall (A B : object * object) (f : product_arrow A B),
      product_arrow_relation A B (product_compose A B B f (product_id B)) f.
  Proof.
    intros [A A'] [B B'] [A_A' B_B'].
    simpl.
    split; apply id_left.
  Defined.

  Definition product_id_right : 
    forall (A B : object * object) (f : product_arrow A B),
      product_arrow_relation A B (product_compose A A B (product_id A) f) f.
  Proof.
    intros [A A'] [B B'] [A_A' B_B'].
    simpl.
    split; apply id_right.
  Defined.

  Definition product_assoc :
    forall (A B C D : Q.(object) * W.(object)) 
        (f : product_arrow A B)
        (g : product_arrow B C) 
        (h : product_arrow C D),
      product_arrow_relation A D
        (product_compose A C D (product_compose A B C f g) h)
        (product_compose A B D f (product_compose B C D g h)).
  Proof.
    intros [A A'] [B B'] [C C'] [D D'] [A_A' B_B'] [B_B'_ C_C'_] [C_C' D_D'].
    simpl.
    split; apply assoc.
  Defined.

  #[export] Instance Category_Product : Category := {
    object := Q.(object) * W.(object);
    arrow := product_arrow;
    compose := product_compose;
    arrow_relation := product_arrow_relation;
    arrow_equiv := product_arrow_equiv;
    cat_compose_proper := product_cat_compose_proper;
    id := product_id;
    id_left := product_id_left;
    id_right := product_id_right;
    assoc := product_assoc;
  }.
End product_cat.
