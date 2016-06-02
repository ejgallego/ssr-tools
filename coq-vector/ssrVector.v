(* (c) Copyright Emilio Jesús Gallego Arias.                            *)
(* You may distribute this file under the terms of the CeCILL-B license *)
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp
Require Import tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* ssreflect interfaces for Coq' stdlib Vector type                           *)
(*                                                                            *)
(* We define a subType structure for vectors, over the same predicate than    *)
(* tuples, that is say, a vector of size n can be seen as a sequence s plus   *)
(* a proof of size s == n.                                                    *)
(*                                                                            *)
(* We can use valP and val_inj on vectors.                                    *)
(*                                                                            *)
(* We provide some lemmas for tuple to vector conversion (and viceversa),     *)
(* even if it does not make much sense to use them over pure tuples.          *)
(*                                                                            *)
(* Some examples are also provided at the end.                                *)
(*                                                                            *)
(* STATUS: experimental, everything will likely change                        *)
(*                                                                            *)
(******************************************************************************)

Require Import Vector.

Section SubVector.

  Section Conv.
  Variables (n : nat) (T : Type).

  Implicit Types (s : seq T).
  Implicit Types (v : t T n).

  Coercion to_list : t >-> seq.

  Definition vP s := size s == n.

  Lemma vtSP v : vP v.
  Proof. by rewrite /vP; elim: v. Defined.

  Definition tvS s (p : vP s) : t T n.
  Proof.
    rewrite /vP in p.
    (* We match on the index n, this is a good compromise to
       keep good reduction behavior... *)
    elim: s n p => [|x s ih] [|n0] // p.
    - exact: nil.
    - exact: cons _ _ _ (ih _ _).
  Defined.
  End Conv.

  Lemma tvSK T n (v : t T n) : tvS (vtSP v) = v.
  Proof. by elim: v => // x n' v ih; rewrite /= ih. Qed.

  Lemma vtSPK T n (s : seq T) (Px : vP n s) : to_list (tvS Px) = s.
  Proof. by elim: n s Px => [ | n ih ] [] // x s Px; rewrite -{2}[s]ih. Qed.

  Lemma vecSub n T : subType (@vP n T).
  Proof.
    apply: (SubType (t T n) (@to_list T n) (@tvS n T)).
    - by move=> K P u; rewrite -[u]tvSK.
    - by move=> x Px; rewrite vtSPK.
  Defined.

  Canonical vec_subType := Eval hnf in vecSub.

  (* EG: Ummm: is this OK? *)
  Canonical vec_tuple T n v := Eval hnf in Tuple (@vtSP n T v).

  (* Lemma k (T : eqType) : [tuple] == [tuple of (@nil T)]. *)
  (* Lemma k (T : eqType) : [tuple] == vec_tuple (@nil T). *)

End SubVector.

Section EqVector.

  Variables (n : nat) (T : eqType).

  Definition vector_eqMixin := Eval hnf in [eqMixin of t T n by <:].
  Canonical  vector_eqType  := Eval hnf in EqType _ vector_eqMixin.

  Canonical vector_predType :=
    Eval hnf in mkPredType (fun t : t T n => mem_seq t).

  (* Lemma f n (T : eqType) (x : T) (v : t T n) : x \in v. *)

End EqVector.

Definition vector_choiceMixin n (T : choiceType) :=
  [choiceMixin of t T n by <:].

Canonical vector_choiceType n (T : choiceType) :=
  Eval hnf in ChoiceType (t T n) (vector_choiceMixin n T).

Definition vector_countMixin n (T : countType) :=
  [countMixin of t T n by <:].

Canonical vector_countType n (T : countType) :=
  Eval hnf in CountType (t T n) (vector_countMixin n T).

Canonical vector_subCountType n (T : countType) :=
  Eval hnf in [subCountType of t T n].

(* Canonical vector_finMixin := Eval hnf in FinMixin (@FinTuple.enumP n T). *)
(* Canonical vector_finType  := Eval hnf in FinType (t T n) vector_finMixin. *)
(* Canonical vector_subFinType := Eval hnf in [subFinType of t T n]. *)

(* Canonical image_vector : #|A|.-tuple T' := [tuple of image f A]. *)
(* Canonical codom_tuple : #|T|.-tuple T' := [tuple of codom f]. *)

(* Canonical vector_subCountType n (T : countType) := *)
(*   Eval hnf in [subCountType of t T n]. *)

Section VecTuple.

  Variable (T : Type).

  Definition tv_def n (u : n.-tuple T) : t T n.
  Proof. by case: u => _ /tvS. Defined.

  Definition tv := nosimpl tv_def.

  Lemma tv_nil : tv [tuple] = (@nil T).
  Proof. by []. Qed.

  Lemma tv_cons n x (xs : n.-tuple T) :
    tv [tuple of x :: xs] = cons _ x _ (tv xs).
  Proof.
    case: xs => xs hxs.
    congr (cons _ _ _ (tvS _)).
    exact: bool_irrelevance.
  Qed.

  (* This definition is nicer when compared to vt' *)
  Definition vt_def n (v : t T n) : n.-tuple T.
  Proof.
    elim: v => [ | x ? ? vt ].
    - exact: [tuple].
    - exact: [tuple of x :: vt].
  Defined.

  Definition vt := nosimpl vt_def.

  Prenex Implicits vt tv.

  Lemma vt_cons n x (xs : t T n) :
    vt (cons _ x _ xs) = [tuple of x :: vt xs].
  Proof. by []. Qed.

  Lemma tvK n : cancel (@vt n) tv.
  Proof.
    elim => [| x ? ? ih ].
    - by [].
    - by rewrite tv_cons ih.
  Qed.

  Lemma vtK n : cancel (@tv n) vt.
  Proof.
    elim: n => [t | n ih t].
    - by rewrite [t]tuple0.
    - by rewrite [t]tuple_eta tv_cons vt_cons (ih (behead_tuple t)).
  Qed.

  Lemma tvI n : injective (@tv n).
  Proof. exact: can_inj (@vtK n). Qed.

  Lemma vtI n : injective (@vt n).
  Proof. exact: can_inj (@tvK n). Qed.

  (* This definition is slightly worse...? *)
  Definition vt' n (v : t T n) : n.-tuple T := Tuple (vtSP v).

  Lemma vt'_cons n x (xs : t T n) :
    vt' (cons _ x _ xs) = [tuple of x :: vt' xs].
  Proof. exact: val_inj. Qed.

End VecTuple.

Module FinVector.
Section FinVector.
Variables (n : nat) (T : finType).

(* Generate all the vectors of size n from T *)
Definition enum_def : seq (t T n) :=
  seq.map (@tv T n) (FinTuple.enum n T).

Definition enum := nosimpl enum_def.

Lemma eq_tv_vt (v : t T n) : [pred x | tv x == v] =1 [pred x | x == vt v].
Proof. by move=> t; rewrite /= -{1}[v]tvK inj_eq //; exact: tvI. Qed.

Lemma enumP : Finite.axiom enum.
Proof.
  move=> t.
  by rewrite count_map (eq_count (eq_tv_vt _)) -(FinTuple.enumP (vt t)).
Qed.

End FinVector.
End FinVector.

Section UseFinVector.

Variables (n : nat) (T : finType).

Canonical vector_finMixin := Eval hnf in FinMixin (@FinVector.enumP n T).
Canonical vector_finType  := Eval hnf in FinType (t T n) vector_finMixin.
Canonical vector_subFinType := Eval hnf in [subFinType of t T n].

End UseFinVector.

(* Experimental stuff: Define a principle to prove things over t A n,
 * but in such a way that the subcases are handled over standard lists
 * plus a size predicate about them
 *)

Section IndVec.

  Definition kk (A : Type) m t (x : A) (H : size t == m) : size (x :: t) == m.+1.
  Proof. by []. Qed.

  Definition vec_rect :
    forall (A : Type) (P : forall n : nat, t A n -> Type),
      (P 0 (nil A)) ->
      (forall (h : A) (n : nat) (t : seq A) (H : size t == n),
         P n (tvS H) -> P n.+1 (tvS (kk h H))) ->
    forall (n : nat) (t : t A n), P n t.
  Proof.
    move=> T P Hnil Hcons n.
    elim: n / => // x n t ih.
    rewrite -[t]tvSK.
    move: (Hcons x n t (vtSP t)).
    rewrite (eq_irrelevance (kk x _) (vtSP _)); apply.
    by rewrite tvSK.
  Qed.

(*
  Definition vec_rect :
    forall (A : Type) (P : forall n : nat, t A n -> Type),
      (P 0 (nil A) ->
      (forall (h : A) (n : nat) (t : t A n), P n t -> P n.+1 (cons A h n t)) ->
    forall (n : nat) (t : t A n), P n t


*)
