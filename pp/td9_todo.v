Require Import ssreflect.
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
(* IF THIS DOES NOT WORK, CALL ME ASAP *)

(* We require function extensionality to have comfortable meta-theory *)
Axiom funext : forall (A : Type) (B : A -> Type) (f g : forall x, B x),
  (forall x, f x = g x) -> f = g.

Implicit Types A B X Y : Set.

(***********************************************************)
(* Replace                                                 *)
(* - `Definition ... Admitted.` by `Definition ... := ...` *)
(* - and `Proof. Admitted.` by an actual proof.            *)
(* - and `Fail .... Admitted.` by an actual proof.         *)
(*                                                         *)
(* Do *not* try to fill Abort. proofs ;)                   *)
(* Now skip the first few sections, that we already saw    *)
(* And go directly to *Lists*                              *)
(***********************************************************)

(********)
(* Bool *)
(********)
Definition ibool := forall X : Set,
   (* true: *) X ->
   (* false: *) X ->
   X.

(* constructors *)
Definition itrue  : ibool := fun X t f => t.
Definition ifalse : ibool := fun X t f => f.

(* destructor *)
Definition ite {X} : ibool -> X -> X -> X := fun b t f => b X t f.

(* negation *)
Definition ineg : ibool -> ibool := fun b X t f => b X f t.

Lemma ineg_true : ineg itrue = ifalse. Proof. by []. Qed.
Lemma ineg_false : ineg ifalse = itrue. Proof. by []. Qed.

(**************************)
(* Church Natural Numbers *)
(**************************)
Definition N : Set := forall X : Set, ( (* S : *) X -> X) -> (* O : *) X -> X.

(* Constructor *)
Definition zero : N := fun X f z => z.
Definition succ : N -> N := fun n X f z => f (n X f z).

(* Destructor *)
Definition N_rec : forall X (s : X -> X) (z : X), N -> X :=
  fun X s z n => n X s z.

(* Programming with Church numerals *)

Definition one := succ zero.
Definition add : N -> N -> N := fun m n X f z => m X f (n X f z).
Definition mul : N -> N -> N := fun m n X f z => m X (n X f) z.
Definition exp : N -> N -> N := fun m n => m N (mul n) one.

(***********)
(* Product *)
(***********)
Definition iprod := fun A B =>
  forall X : Set, ((* ipair : *) A -> B -> X) -> X.

(* constructor *)
Definition ipair {A B : Set} : A -> B -> iprod A B := fun a b X f => f a b.

(* destructors *)
Definition ifst {A B : Set} : iprod A B -> A := fun w => w A (fun a b => a).
Definition isnd {A B : Set} : iprod A B -> B := fun w => w B (fun a b => b).

(* equations *)
Lemma ifst_ipair A B (a : A) (b : B) : ifst (ipair a b) = a. Proof. by []. Qed.
Lemma isnd_ipair A B (a : A) (b : B) : isnd (ipair a b) = b. Proof. by []. Qed.

(* unprovable *)
(* DO NOT ATTEMPT TO PROVE THIS, IT IS NOT TRUE! *)
Lemma iprod_eta A B (w : iprod A B) : ipair (ifst w) (isnd w) = w.
(* DO NOT ATTEMPT TO PROVE THIS, IT IS NOT TRUE! *)
Proof.
(* we cannot inspect w *)
(* DO NOT ATTEMPT TO PROVE THIS, IT IS NOT TRUE! *)
Abort.

(* however if w is an ipair, this becomes trivial *)
Lemma iprod_eta_pairs A B (a : A) (b : B) (w := ipair a b) :
  ipair (ifst w) (isnd w) = w.
Proof. by []. Qed.

(*********)
(* Lists *)
(*********)
Definition ilist A : Set := forall Y, Y -> (A -> Y -> Y) -> Y.

(* Constructors *)
Definition inil : forall A, ilist A := fun A Y y f => y.
Definition icons : forall A, A -> ilist A -> ilist A :=
  fun A a l Y y f => f a (l Y y f).

(* Destructor *)

(* Write down the type of list's destructor *)
Definition fold_type : Type :=
  forall X Y, Y -> (X -> Y -> Y) -> ilist X -> Y.
(* Program it *)
Definition ifold : fold_type := fun X Y y f l =>
  l Y y f.

Definition imap : forall X Y, (X -> Y) -> (ilist X -> ilist Y) :=
  fun X Y f l =>
  ifold X (ilist Y) (inil Y) (fun x a => icons Y (f x) a) l.

Example imap_ex X Y (f : X -> Y) (x : X) (y : X) :
  imap X Y f (icons X x (icons X y (inil X)))
  = icons Y (f x) (icons Y (f y) (inil Y)).
Proof. reflexivity. Qed.

Definition ilength : forall X, ilist X -> N :=
  fun X l => ifold X N zero (fun _ => succ) l.

(*********)
(* Trees *)
(*********)

Definition itree A : Set := forall Y, (A -> Y) -> (Y -> Y -> Y) -> Y.

(* Constructors *)
Definition ileaf : forall A, A -> itree A := fun A a Y f g => f a.
Definition ibinNode : forall A, itree A -> itree A -> itree A := fun A u v Y f g =>
  g (u Y f g) (v Y f g).

(* Destructor *)

(* Write down the type of tree's destructor *)
Definition ifoldTree_type : Type :=
  forall A Y, (A -> Y) -> (Y -> Y -> Y) -> itree A -> Y.
(* Program it *)
Definition ifoldTree : ifoldTree_type :=
  fun A Y f g u => u Y f g.

Definition iconcat : forall X, ilist X -> ilist X -> ilist X :=
  fun X l l' => ifold X (ilist X) l' (fun x a => icons X x a) l.

Definition iflatten : forall X, itree X -> ilist X :=
  fun X u =>
  u (ilist X) (fun x => icons X x (inil X)) (iconcat X).

(***************)
(* Existential *)
(***************)

Implicit Types (V : Set -> Set) (U W : Set).

Definition iexists V : Set. Admitted.
Notation "'Σ' X , V" := (iexists (fun X => V))
  (format "'Σ' X ,  V", X name, at level 99).

(* Define its constructor and destructor *)

(******************************)
(* Generating Church integers *)
(******************************)

(* producing Church integers *)
Definition Church : nat -> N . Admitted.

(* producing nat from N *)
Definition N2nat : N -> nat . Admitted.

(* The "Church" function is injective *)
Lemma ChurchK n : N2nat (Church n) = n. Admitted.

(* The converse is not true:
   several elements of N may represent the same Church integer!!! *)
(* DO NOT ATTEMPT TO PROVE THIS, IT IS NOT TRUE! *)
Lemma N2natK n : Church (N2nat n) = n.
(* DO NOT ATTEMPT TO PROVE THIS, IT IS NOT TRUE! *)
Proof.
(* DO NOT ATTEMPT TO PROVE THIS, IT IS NOT TRUE! *)
apply/funext => X; apply/funext => f; apply/funext => z /=.
(* DO NOT ATTEMPT TO PROVE THIS, IT IS NOT TRUE! *)
Abort.


