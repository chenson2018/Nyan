Set Printing Projections.
Require Export Setoid.
Require Export Morphisms.
Require Export Classes.RelationClasses.

Declare Scope category_scope.
Delimit Scope category_scope with Cat.
Open Scope category_scope.

Reserved Infix "≈"  (at level 79).
Reserved Infix "∘"  (at level 40, left associativity).
Reserved Infix "~>" (at level 90, right associativity).

Class Category : Type := {
  object: Type;

  (* here I let Coq lift Type to a higher universe, might do it explicitly later *)
  arrow: object -> object -> Type
    where "a ~> b" := (arrow a b);

  compose {A B C} (f: A ~> B) (g: B ~> C): 
    A ~> C 
    where "g ∘ f" := (compose f g);

  arrow_relation {A B}: relation (A ~> B)
    where "f ≈ g" := (arrow_relation f g);

  arrow_equiv {A B} : Equivalence (@arrow_relation A B);

  cat_compose_proper {A B C: object}: 
    Proper 
    (
      (@arrow_relation A B) ==> 
      (@arrow_relation B C) ==> 
      (@arrow_relation A C)
    ) 
    (@compose A B C);

  id {A}: 
    A ~> A;

  id_left {A B} (f: A ~> B): 
    id ∘ f ≈ f;
  
  id_right {A B} (f: A ~> B): 
    f ∘ id ≈ f;

  assoc {A B C D} (f: A ~> B) (g: B ~> C) (h: C ~> D): 
      h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f;

  domain   {A B} (f : A ~> B) := A;
  codomain {A B} (f : A ~> B) := B;     
}.

Notation "f ≈ g" := (arrow_relation f g) (at level 79) : category_scope.
Notation "g ∘ f"    := (compose f g) (at level 40, left associativity): category_scope.
Notation "f ~> g"   := (arrow f g) (at level 90, right associativity): category_scope.

(* 
   every Category comes with proofs that 
    - there is an equivalence relation for its arrows
    - this relation can rewrite across composition 

   these polymorphic instances then allow rewriting for any category!
*)
#[export] Instance Category_relation_Equivalence (Cat: Category) (A B: object) : Equivalence (@arrow_relation Cat A B).
Proof. apply arrow_equiv. Qed.

#[export] Instance Category_compose_morphism (Cat : Category) (A B C: object) : 
  Proper 
  (
    (@arrow_relation Cat A B) ==> 
    (@arrow_relation Cat B C) ==> 
    (@arrow_relation Cat A C)
  ) 
  (@compose Cat A B C).
Proof. apply cat_compose_proper. Qed.

Close Scope category_scope.
