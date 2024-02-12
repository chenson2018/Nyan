Require Import Nyan.Theory.Category.
Open Scope Cat.

Section functor.
  Variables C D : Category.

  Class Functor (C D :Category) := {
    functor_map : 
      C.(object) -> D.(object);

    functor_arr {A B} : 
      A ~> B -> functor_map A ~> functor_map B;

    functor_id {A} : functor_arr (@id C A) ≈ id;

    functor_compose {A B C} (f: A ~> B) (g: B ~> C):
      functor_arr (g ∘ f) ≈ functor_arr g ∘ functor_arr f
  }.
End functor.
