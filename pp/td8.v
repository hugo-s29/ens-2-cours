Require Import ssreflect.
Require Import NArith.
Set Universe Polymorphism.

(****************************************************************************)
(* BEWARE                                                                   *)
(* In order to emulate system F in Coq/Rocq, we have to activate the option *)
(* `-impredicative-set` when running coqc/coqtop.                           *)
(* Add a `_CoqProject` file in your directory with the following contents:  *)
(* ```                                                                      *)
(* -arg -impredicative-set                                                  *)
(* ```                                                                      *)
(****************************************************************************)
(* This tests that you activated the option correctly *)
Check (forall X : Set, X) : Set.

(* We require function extensionality to have comfortable meta-theory *)
Axiom funext : forall (A : Type) (B : A -> Type) (f g : forall x, B x),
  (forall x, f x = g x) -> f = g.

Implicit Types A B X Y : Set.

(***********************************************************)
(* Replace                                                 *)
(* - `Definition ... Admitted.` by `Definition ... := ...` *)
(* - and `Proof. Admitted.` by an actual proof.            *)
(*                                                         *)
(* Do *not* try to fill Abort. proofs ;)                   *)
(***********************************************************)

(********)
(* Bool *)
(********)
Definition ibool := forall X : Set,
   (* true: *) X ->
   (* false: *) X ->
   X.

(* constructors *)
Definition itrue  : ibool := fun X x y => x.
Definition ifalse : ibool := fun X x y => y.

(* destructor *)
Definition ite {X} : ibool -> X -> X -> X := fun x => x X.

(***********)
(* Product *)
(***********)
Definition iprod := fun A B =>
  forall X : Set, ((* ipair : *) A -> B -> X) -> X.

(* constructor *)
Definition ipair {A B : Set} : A -> B -> iprod A B := fun a b X f => f a b.

(* destructors *)
Definition ifst {A B : Set} : iprod A B -> A := fun p => p A (fun x y => x).
Definition isnd {A B : Set} : iprod A B -> B := fun p => p B (fun x y => y).

(* equations *)
Lemma ifst_ipair A B (a : A) (b : B) : ifst (ipair a b) = a.
Proof eq_refl.

Lemma isnd_ipair A B (a : A) (b : B) : isnd (ipair a b) = b.
Proof eq_refl.

(* unprovable *)
Lemma iprod_eta A B (w : iprod A B) : ipair (ifst w) (isnd w) = w.
Proof. Abort.

(* however if w is an ipair, this becomes trivial *)
Lemma iprod_eta_pairs A B (a : A) (b : B) (w := ipair a b) :
  ipair (ifst w) (isnd w) = w.
Proof eq_refl.


(*******************)
(* Natural numbers *)
(*******************)
Definition N : Set := forall (X : Set), (X -> X) -> (X -> X).

(* Constructor *)
Definition zero : N := fun X f x => x.
Definition succ : N -> N := fun n X f x => f (n X f x).

(* Destructor *)
(* Write down the type of N's destructor *)
Definition N_rec_type : Type := forall (X : Set), (X -> X) -> X -> N -> X.
(* Program it *)
Definition N_rec : N_rec_type := fun X f x n => n X f x.

(* Programming with Church integers *)
Definition one : N := succ zero.
Definition add : N -> N -> N := fun n m => N_rec N succ n m.
Definition mul : N -> N -> N := fun n m => N_rec N (add m) zero n.
Definition exp : N -> N -> N := fun n m => N_rec N (mul n) one m.

(***************************)
(* Programming predecessor *)
(***************************)

(* Write the predecessor function, do not hesitate to
   create subroutine(s) *)

Definition update_pair : iprod N N -> iprod N N :=
  fun p => ipair (succ (isnd p)) (ifst p).

Definition pred : N -> N :=
  fun n =>
  isnd (N_rec (iprod N N) update_pair (ipair zero zero) n).

Eval cbv in pred (succ one).

(******************************)
(* Generating Church integers *)
(******************************)

(* producing Church integers *)
Definition Church : nat -> N :=
  fix f (n : nat) :=
    match n with
    | O   => zero
    | S k => succ (f k)
    end.

(* producing nat from N *)
Definition N2nat : N -> nat := N_rec nat S O.

(* The "Church" function is injective *)
Lemma ChurchK n : N2nat (Church n) = n.
Proof.
  induction n.
  - apply eq_refl.
  - assert (S (N2nat (Church n)) = N2nat (succ (Church n))).
    + apply eq_refl.
    + simpl; rewrite <- H; rewrite IHn; apply eq_refl.
Qed.



(* The converse is not true:
   several elements of N may represent the same Church integer!!! *)
Lemma N2natK n : Church (N2nat n) = n.
Proof.
  apply/funext => X; apply/funext => f; apply/funext => z /=.
Abort.

(*******************************************)
(* Theorems about Church integers programs *)
(*******************************************)

Lemma zero_correct : zero = Church 0. Proof eq_refl.

Lemma one_correct : one = Church 1. Proof eq_refl.

Lemma test_add : add (Church 3) (Church 4) = Church 7. Proof eq_refl.

Lemma test_mul : mul (Church 3) (Church 4) = Church 12. Proof eq_refl.

Lemma add_zero_n n : add zero (Church n) = (Church n).
Proof.
  induction n.
  - apply eq_refl.
  - simpl.
    assert (add zero (succ (Church n)) = succ (add zero (Church n))) by apply eq_refl.
    rewrite H; rewrite IHn; apply eq_refl.
Qed.




Lemma add_n_zero n : add (Church n) zero = (Church n). Proof.
  induction n.
  - apply eq_refl.
  - simpl.
    assert (add (succ (Church n)) zero = succ (add (Church n) zero)) by apply eq_refl.
    rewrite H; rewrite IHn; apply eq_refl.
Qed.

Lemma add_succ_n m n :
  add (succ (Church m)) (Church n) = succ (add (Church m) (Church n)).
Proof.
  induction n.
  - apply eq_refl.
  - simpl.
    assert (succ (add (Church m) (succ (Church n))) = succ (succ (add (Church m) (Church n)))) by apply eq_refl.
    rewrite H; rewrite <- IHn; apply eq_refl.
Qed.

Lemma mul_succ_n m n :
  mul (succ (Church m)) (Church n) = add (Church n) (mul (Church m) (Church n)).
Proof.
  induction m; apply eq_refl.
Qed.

Lemma succ_correct n : succ (Church n) = Church (S n). Proof eq_refl.

Lemma add_correct m n : add (Church m) (Church n) = Church (m + n).
Proof.
  induction m.
  - apply add_zero_n.
  - assert (Church (S m + n) = succ (Church (m + n))) by exact eq_refl.
    rewrite H; rewrite <- IHm; simpl; apply add_succ_n.
Qed.


Lemma mul_correct m n : mul (Church m) (Church n) = Church (m * n).
Proof. 
  induction m.
  - apply eq_refl.
  - rewrite mul_succ_n; rewrite IHm.
    

Lemma exp_correct m n : exp (Church n) (Church m) = Church (Nat.pow m n).
Proof. Admitted.

Lemma pred_correct (m : nat) : pred (Church (S m)) = Church m.
Proof. Admitted.
