(* Coq Imports *)
Require Import Structures.Equalities Structures.Orders.
Require Import MSets.

(* SSR Imports *)
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp
Require Import choice fintype finset.

(* External *)
Require Import finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Example of equivalence for MSets/{finset} *)

(* This is a bit of pain, must do it better. *)
Module MakeFinOrd <: OrderedType.

(* Parameter (T : finOrdType). *)
Parameter (T : finType).
Implicit Types (x y : T).

Definition t : Type := T.
Definition eq := (@eq T).

Lemma eq_dec x y : {x = y} + {x <> y}.
Proof. exact: decP eqP. Qed.

(* I couldn't find this in Coq... *)
Lemma eq_equiv : Equivalence eq.
Proof. by constructor; rewrite /eq; auto; move=> x y z ->. Qed.

(* Lt *)
Definition lt (x y : T) : Prop.
Admitted.

Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
Admitted.

Lemma lt_strorder : StrictOrder lt.
Admitted.

Definition compare (x y : T) : comparison.
Admitted.

Lemma compare_spec x y :
  CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
Proof.
Admitted.

End MakeFinOrd.

Module ES := MSetAVL.Make(MakeFinOrd).

(* Now we prove the equivs. *)
Section SetEquiv.

Import ES.

Implicit Types (e : t) (i : {set elt}).

Definition eqS e i := forall x, reflect (In x e) (x \in i).

Lemma eqE e1 e2 i1 i2 (h1 : eqS e1 i1) (h2 : eqS e2 i2) :
  reflect (Equal e1 e2) (i1 == i2).
Proof.
apply: (iffP eqP) => [H x|H]; [split|].
  + by move/h1=> p1; apply/h2; rewrite -H.
  + by move/h2=> p2; apply/h1; rewrite H.
apply/setP=> i; apply/idP/idP.
+ by move/h1=> p1; apply/h2/H.
+ by move/h2=> p2; apply/h1/H.
Qed.

Implicit Arguments eqE [e1 e2 i1 i2].
Prenex Implicits eqE.

Lemma equal_specP e1 e2 : reflect (Equal e1 e2) (equal e1 e2).
Proof. by apply: (iffP idP); move/equal_spec. Qed.

Lemma eqbE e1 e2 i1 i2 (h1 : eqS e1 i1) (h2 : eqS e2 i2) :
  (equal e1 e2) = (i1 == i2).
Proof. exact/equal_specP/(eqE h1 h2). Qed.

Lemma subsetE e1 e2 i1 i2 (h1 : eqS e1 i1) (h2 : eqS e2 i2) :
  reflect (Subset e1 e2) (i1 \subset i2).
Proof. by apply: (iffP subsetP) => H s /h1/H/h2. Qed.

(* Arguments subsetE [e1 e2 i1 i2 h1 h2]. *)
(* Prenex Implicits subsetE. *)

Lemma subset_specP e1 e2 : reflect (Subset e1 e2) (subset e1 e2).
Proof. by apply: (iffP idP); move/subset_spec. Qed.

Lemma subsetEb e1 e2 i1 i2 (h1 : eqS e1 i1) (h2 : eqS e2 i2) :
  subset e1 e2 = (i1 \subset i2).
Proof. exact/subset_specP/(subsetE h1 h2). Qed.

Lemma emptyE e i (p : eqS e i) :
  reflect (Empty e) (i == set0).
Proof.
apply: (iffP eqP) => H.
  by move=> x /p; rewrite H inE.
by apply/setP=> k; apply/idP/idP; [move/p/H | rewrite inE].
Qed.

Implicit Arguments emptyE [e i p].
Prenex Implicits emptyE.

Lemma is_empty_specP s : reflect (Empty s) (is_empty s).
Proof. by apply: (iffP idP); move/is_empty_spec. Qed.

Lemma emptyEb e i (h : eqS e i) :
  (is_empty e) = (i == set0).
Proof. exact/is_empty_specP/emptyE. Qed.

Lemma addE e i (p : eqS e i) x : eqS (add x e) (x |: i).
Proof.
by move=> y; apply: (iffP setU1P); rewrite add_spec; case=> [->|/p hp]; auto.
Qed.

Lemma unionE e1 e2 i1 i2 (h1 : eqS e1 i1) (h2 : eqS e2 i2) :
  eqS (union e1 e2) (i1 :|: i2).
Proof.
by move=> y; apply: (iffP setUP); rewrite union_spec; case=> [/h1|/h2]; auto.
Qed.

Lemma interE e1 e2 i1 i2 (h1 : eqS e1 i1) (h2 : eqS e2 i2) :
  eqS (inter e1 e2) (i1 :&: i2).
Proof.
by move=> y; apply: (iffP setIP); rewrite inter_spec; case=> /h1 ? /h2 ?.
Qed.

End SetEquiv.

(* This is a bit of pain, must do it better. *)
Variable (U : choiceType).
Variable (ltU : rel U).

Module Uord <: OrderedType.
  Definition t : Type := U.

  (* Eq *)
  Definition eq := (@eq U).
  Lemma eq_dec x y :{eq x y} + {~ eq x y}.
  Admitted.
  Lemma eq_equiv : Equivalence eq.
  Admitted.

  (* Lt *)
  Definition lt (x y : U) : Prop := ltU x y.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Admitted.

  Lemma lt_strorder : StrictOrder lt.
  Admitted.

  (* Comp *)
  Definition compare (x y : U) :=
    if ltU x y then Lt else if x == y then Eq else Gt.

  Lemma compare_spec x y :
    CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
  Admitted.
End Uord.

Module ESU := MSetAVL.Make(Uord).

(* We use a module to have namespaces *)
Module FSetEquiv.

Import ESU.

Local Open Scope fset.
Implicit Types (e : t) (i : {fset elt}).

Definition inE := (inE, in_fsetE).

Definition eqS e i := forall x, reflect (In x e) (x \in i).

Lemma eqE e1 e2 i1 i2 (h1 : eqS e1 i1) (h2 : eqS e2 i2) :
  reflect (Equal e1 e2) (i1 == i2).
Proof.
apply: (iffP eqP) => [H x|H].
  split.
  + by move/h1=> p1; apply/h2; rewrite -H.
  + by move/h2=> p2; apply/h1; rewrite H.
apply/fsetP=> i; apply/idP/idP.
+ by move/h1=> p1; apply/h2/H.
+ by move/h2=> p2; apply/h1/H.
Qed.

Implicit Arguments eqE [e1 e2 i1 i2].
Prenex Implicits eqE.

Lemma equal_specP e1 e2 : reflect (Equal e1 e2) (equal e1 e2).
Proof. by apply/(iffP idP); move/equal_spec. Qed.

Lemma eqbE e1 e2 i1 i2 (h1 : eqS e1 i1) (h2 : eqS e2 i2) :
  (equal e1 e2) = (i1 == i2).
Proof. exact/equal_specP/(eqE h1 h2). Qed.

Implicit Arguments fsubsetP [K A B].
Lemma subsetE e1 e2 i1 i2 (h1 : eqS e1 i1) (h2 : eqS e2 i2) :
  reflect (Subset e1 e2) (i1 `<=` i2).
Proof. by apply: (iffP fsubsetP) => H s /h1 /H /h2. Qed.

(* Arguments subsetE [e1 e2 i1 i2 h1 h2]. *)
(* Prenex Implicits subsetE. *)

Lemma subset_specP e1 e2 : reflect (Subset e1 e2) (subset e1 e2).
Proof. by apply: (iffP idP); move/subset_spec. Qed.

Lemma subsetEb e1 e2 i1 i2 (h1 : eqS e1 i1) (h2 : eqS e2 i2) :
  subset e1 e2 = (i1 `<=` i2).
Proof. exact/subset_specP/(subsetE h1 h2). Qed.

Lemma emptyE e i (p : eqS e i) :
  reflect (Empty e) (i == fset0).
Proof.
apply: (iffP eqP) => H.
  by move=> x /p; rewrite H inE.
by apply/fsetP=> k; apply/idP/idP; [move/p/H|rewrite inE].
Qed.

Implicit Arguments emptyE [e i p].
Prenex Implicits emptyE.

Lemma is_empty_specP s : reflect (Empty s) (is_empty s).
Proof. by apply: (iffP idP); move/is_empty_spec. Qed.

Lemma emptyEb e i (h : eqS e i) :
  (is_empty e) = (i == fset0).
Proof. exact/is_empty_specP/emptyE. Qed.

Implicit Arguments fset1UP [K x a B].

Lemma addE e i (p : eqS e i) x : eqS (add x e) (x |` i).
Proof.
by move=> y; apply: (iffP fset1UP); rewrite add_spec; case=> [->|/p hp]; auto.
Qed.

Implicit Arguments fsetUP [K x A B].
Lemma unionE e1 e2 i1 i2 (h1 : eqS e1 i1) (h2 : eqS e2 i2) :
  eqS (union e1 e2) (i1 `|` i2).
Proof.
by move=> y; apply: (iffP fsetUP); rewrite union_spec; case=> [/h1|/h2]; auto.
Qed.

Implicit Arguments fsetIP [K x A B].
Lemma interE e1 e2 i1 i2 (h1 : eqS e1 i1) (h2 : eqS e2 i2) :
  eqS (inter e1 e2) (i1 `&` i2).
Proof.
by move=> y; apply: (iffP fsetIP); rewrite inter_spec; case=> /h1 ? /h2 ?.
Qed.

End FSetEquiv.

Print Assumptions interE.
