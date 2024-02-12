Require Import Nyan.Theory.Category.
Require Import Nyan.Theory.Ism.
Require Import Nyan.Theory.Dual.
Open Scope Cat.

Class Initial {Cat : Category} := {
  Zero : Cat.(object);
  initial_arrow: forall A, Zero ~> A;
  initial_unique: forall A (f f' : Zero ~> A), f ≈ f';
}.

Class Terminal {Cat : Category} := {
  One : Cat.(object);
  terminal_arrow: forall A, A ~> One;
  terminal_unique: forall A (f f' : A ~> One), f ≈ f';
}.

Lemma Terminal_Iso {Cat: Category} (T T': Terminal) (f: T.(One) ~> T'.(One)) : Iso f.
Proof.
  destruct T  as [One_T  terminal_arrow_T  terminal_unique_T ].
  destruct T' as [One_T' terminal_arrow_T' terminal_unique_T'].
  simpl in *.
  apply Build_Iso with (terminal_arrow_T One_T').
  - apply terminal_unique_T.
  - apply terminal_unique_T'.
Qed.

Lemma Initial_Iso {Cat: Category} (T T': Initial) (f: T.(Zero) ~> T'.(Zero)) : Iso f.
Proof.
  destruct T  as [Zero_T  initial_arrow_T  initial_unique_T ].
  destruct T' as [Zero_T' initial_arrow_T' initial_unique_T'].
  simpl in *.
  apply Build_Iso with (initial_arrow_T' Zero_T).
  - apply initial_unique_T.
  - apply initial_unique_T'.
Qed.

(* show that these are dual concepts *)
(* TODO use this to prove the above, and maybe a more general technique for dual proofs *)

Lemma Dual_Initial_Terminal 
  {Cat: Category} 
  (I : @Initial Cat)
  (T : @Terminal (Category_Dual Cat))
  (f: I.(Zero) ~> T.(One))
  : Iso f. 
Proof.
  destruct I as [Zero_I initial_arrow_I  initial_unique_I ].
  destruct T as [One_T  terminal_arrow_T terminal_unique_T].
  simpl in *.
  apply Build_Iso with (terminal_arrow_T Zero_I).
  - apply initial_unique_I.
  - apply terminal_unique_T.
Qed.

Class Product {Cat: Category} := {
  p_A   : object;
  p_B   : object;
  p_C   : object;
  p_AxB : object;
  p_f   : p_C ~> p_A;
  p_g   : p_C ~> p_B;
  p_med : p_C ~> p_AxB;
  pi_1  : p_AxB ~> p_A;
  pi_2  : p_AxB ~> p_B;
  p_med_unique : forall med': p_C ~> p_AxB, p_med ≈ med';
  pi_1_comm : pi_1 ∘ p_med ≈ p_f;
  pi_2_comm : pi_2 ∘ p_med ≈ p_g;
}.

Class CoProduct {Cat: Category} := {
  cop_A   : object;
  cop_B   : object;
  cop_C   : object;
  cop_ApB : object;
  cop_f   : cop_A ~> cop_C;
  cop_g   : cop_B ~> cop_C;
  cop_med : cop_ApB ~> cop_C;
  iota_1  : cop_A ~> cop_ApB;
  iota_2  : cop_B ~> cop_ApB;
  cop_med_unique : forall med', cop_med ≈ med';
  iota_1_comm : cop_med ∘ iota_1 ≈ cop_f;
  iota_2_comm : cop_med ∘ iota_2 ≈ cop_g;
}.
