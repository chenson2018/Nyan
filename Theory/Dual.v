Require Import Nyan.Theory.Category. 
Open Scope Cat.

(* The category with reversed arrows *)

Section cat_dual.
  Context (Cat: Category).
  
  Lemma Proper_dual:
  forall A B C : object,
    Proper
      (arrow_relation ==> arrow_relation ==> arrow_relation)
      (fun (BA : B ~> A) (CB : C ~> B) => BA ∘ CB).
  Proof.
    intros.
    unfold Proper, respectful.
    intros.
    rewrite H, H0.
    reflexivity.
  Qed.
  
  Lemma Assoc_dual : forall 
      (A B C D : object) 
      (f : B ~> A) 
      (g : C ~> B) 
      (h : D ~> C),
    f ∘ g ∘ h ≈ f ∘ (g ∘ h).
  Proof. intros. rewrite assoc. reflexivity. Qed.
    
  #[export] Instance Category_Dual: Category := {
    object := object;
    arrow := fun A B => B ~> A;
    compose := fun A B C BA CB => BA ∘ CB ;
    arrow_relation := fun A B => arrow_relation;
    arrow_equiv := fun A B => arrow_equiv;
    cat_compose_proper := Proper_dual;
    id := fun A => id;
    id_left := fun A B f => id_right f;
    id_right := fun A B f => id_left f;
    assoc := Assoc_dual;
  }.
End cat_dual.
