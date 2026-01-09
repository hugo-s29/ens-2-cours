Module ShallowNJ.

Implicit Types A B C : Prop.

Lemma NegE A : ~ A -> A -> False. Proof. intuition. Qed.
Lemma AndE1 B A : A /\ B -> A. Proof. intuition. Qed.
Lemma AndE2 A B : A /\ B -> B. Proof. intuition. Qed.
Lemma OrE A B C : A \/ B -> (A -> C) -> (B -> C) -> C. Proof. intuition. Qed.
Lemma ImplyE A B : A -> (A -> B) -> B. Proof. intuition. Qed.

Ltac Ax := assumption.
Ltac TopI := exact I.
Ltac BotE := exfalso.
Ltac NegI := intro.
Ltac NegE A := apply (NegE A).
Ltac AndI := split.
Ltac AndE1 B := apply (AndE1 B).
Ltac AndE2 B := apply (AndE2 B).
Ltac OrI1 := left.
Ltac OrI2 := right.
Ltac OrE A B := apply (OrE A B); [|intro|intro].
Ltac ImplyI := intro.
Ltac ImplyE A := apply (ImplyE A).

Notation "A ∨ B" := (A \/ B) (at level 85) : type_scope.
Notation "A ∧ B" := (A /\ B) (at level 80) : type_scope.
Notation "A ⇒ B" := (A -> B) (right associativity, at level 99) : type_scope.
Notation "¬ A" := (~ A) (at level 75) : type_scope.
Notation "⊤" := (True) : type_scope.
Notation "⊥" := (False) : type_scope.


Module Ex1.
    Goal forall A B C, (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C).
    Proof.
      intros A B C.
      ImplyI.
      ImplyI.
      ImplyI.
      ImplyE B.
      ImplyE A.
      Ax.
      Ax.
      ImplyE A.
      Ax.
      Ax.
    Qed.

    Goal forall A B C, (A ∧ B) ∨ (A ∧ C) ⇒ A ∧ (B ∨ C). 
    Proof.
      intros A B C.
      ImplyI.
      OrE (A ∧ B) (A ∧ C).
      Ax.
      AndI.
      AndE1 B.
      Ax.
      OrI1.
      AndE2 A.
      Ax.
      AndI.
      AndE1 C.
      Ax.
      OrI2.
      AndE2 A.
      Ax.
    Qed.
    
End Ex1.

Module Ex2.
  Goal forall A B, ¬(A ∨ B) ⇒ (¬A ∧ ¬B).
  Proof.
    intros A B.
    ImplyI.
    AndI.
    all: NegI.
    all: NegE (A ∨ B).
    Ax.
    OrI1.
    Ax.
    Ax.
    OrI2.
    Ax.
  Qed.
End Ex2.

Module Ex8.
  Goal forall A, A ⇒ ¬¬ A.
  Proof.
    intro A.
    ImplyI.
    NegI.
    NegE A; Ax.
  Qed.

  Goal forall A, ¬ (A ∧ ¬ A).
  Proof.
    intro A.
    NegI.
    NegE A; [AndE2 A | AndE1 (¬ A)]; Ax.
  Qed.

  Goal forall A, (¬¬¬A) ⇒ ¬A.
  Proof.
    intro A.
    NegI.
    NegI.
    NegE (¬¬A).
    Ax.
    NegI.
    NegE A; Ax.
  Qed.

  Goal forall A, ¬¬ (A ∨ ¬ A).
  Proof.
    intro A.
    NegI.
    NegE (¬A); NegI.
    - NegE (A ∨ ¬ A).
      Ax.
      OrI2.
      Ax.
    - NegE (A ∨ ¬ A).
      Ax.
      OrI1.
      Ax.
  Qed.

End Ex8.

Module Ex9.
  Definition cond R := ¬ R.
  Definition thing A R : Prop := A ⇒ R.

  Goal forall R, cond R <-> forall A, thing A R <-> ¬ A.
  Proof.
    intro R.
    split; [intros H A| intro H].
    - split; ImplyI. 
      * NegI; NegE R; [| ImplyE A]; Ax.
      * ImplyI. BotE. NegE A; Ax.
    - specialize (H R).
      apply H.
      ImplyI.
      Ax.
  Qed.
End Ex9.

End ShallowNJ.
