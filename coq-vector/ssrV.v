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
(* ssreflect interfaces for Vector type                                       *)
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

Fixpoint V (n : nat) T {struct n} : Type :=
  match n with
  | 0    => unit
  | n.+1 => (T * V n T)%type
  end.

Definition vnil  {T} : V 0 T := tt.
Definition vcons {T n} (x : T) (v : V n T) : V n.+1 T := (x,v).

Definition v_class n T := V n T.
Identity Coercion v_of_vclass : v_class >-> V.

Definition to_list {n T} (v : V n T) : seq T.
elim: n v => [_|n /= ihn [x]]; first exact: [::].
by move/ihn/(cons x); apply.
Defined.

Section SubVector.

  Section Conv.
  Variables (n : nat) (T : Type).

  Implicit Types (s : seq T).
  Implicit Types (v : V n T).

  (* XXX: Fix this coercion *)
  Coercion to_list : V >-> seq.

  Definition vP s := size s == n.

  Lemma vtSP v : vP v.
  Proof. rewrite /vP; elim: n v => //= n' ihn [x v] /=.
         exact: (ihn v).
  Defined.

  Definition tvS s (p : vP s) : V n T.
  Proof.
    rewrite /vP in p.
    (* We match on the index n, this is a good compromise to
       have reduction... *)
    elim: s n p => [|x s ih] [|n0] // p.
    exact: vcons _ (ih _ _).
  Defined.
  End Conv.

  Lemma tvSK T n (v : V n T) : tvS (vtSP v) = v.
  Proof. by elim: n v => [[//]|n ihn [x v]]; rewrite /= ihn. Qed.

  Lemma vtSPK T n (s : seq T) (Px : vP n s) : s = tvS Px.
  Proof. by elim: n s Px => [ | n ih ] [] //= x s Px; rewrite {1}[s]ih. Qed.

  Lemma vecSub n T : subType (@vP n T).
  Proof.
    apply: (SubType (V n T) (@to_list n T) (@tvS n T)).
    - by move=> K P u; rewrite -[u]tvSK.
    - by move=> x Px; rewrite -vtSPK.
  Defined.

  Canonical V_subType := Eval hnf in vecSub.

  (* EG: Ummm: is this OK? *)
  Canonical V_tuple T n v := Eval hnf in Tuple (@vtSP n T v).

  (* Lemma k (T : eqType) : [tuple] == [tuple of (@vnil T)]. *)
  (* Lemma k' (T : eqType) : [tuple] == V_tuple (@vnil T). *)

End SubVector.

Section EqVector.

  Variables (n : nat) (T : eqType).

  Definition vector_eqMixin := Eval hnf in [eqMixin of V n T by <:].
  Canonical  vector_eqType  := Eval hnf in EqType _ vector_eqMixin.

  Canonical vector_predType :=
    Eval hnf in mkPredType (fun t : V n T => mem_seq (to_list t)).

  (* Lemma f n (T : eqType) (x : T) (v : V n T) : x \in v. *)

End EqVector.

Definition vector_choiceMixin n (T : choiceType) :=
  [choiceMixin of V n T by <:].

Canonical vector_choiceType n (T : choiceType) :=
  Eval hnf in ChoiceType (V n T) (vector_choiceMixin n T).

Definition vector_countMixin n (T : countType) :=
  [countMixin of V n T by <:].

Canonical vector_countType n (T : countType) :=
  Eval hnf in CountType (V n T) (vector_countMixin n T).

Canonical vector_subCountType n (T : countType) :=
  Eval hnf in [subCountType of V n T].

(* Canonical vector_finMixin := Eval hnf in FinMixin (@FinTuple.enumP n T). *)
(* Canonical vector_finType  := Eval hnf in FinType (V n T) vector_finMixin. *)
(* Canonical vector_subFinType := Eval hnf in [subFinType of V n T]. *)

(* Canonical image_vector : #|A|.-tuple T' := [tuple of image f A]. *)
(* Canonical codom_tuple : #|T|.-tuple T' := [tuple of codom f]. *)

(* Canonical vector_subCountType n (T : countType) := *)
(*   Eval hnf in [subCountType of V n T]. *)

Section VecTuple.

  Variable (T : Type).

  Definition tv_def n (u : n.-tuple T) : V n T.
  Proof. by case: u => _ /tvS. Defined.

  Definition tv := nosimpl tv_def.

  Lemma tv_nil : tv [tuple] = (@vnil T).
  Proof. by []. Qed.

  Lemma tv_cons n x (xs : n.-tuple T) :
    tv [tuple of x :: xs] = vcons x (tv xs).
  Proof.
    case: xs => xs hxs.
    congr (vcons _ (tvS _)).
    exact: bool_irrelevance.
  Qed.

  (* This definition is nicer when compared to vt' *)
  Definition vt_def n (v : V n T) : n.-tuple T.
  Proof.
    elim: n v => [ ? | n ihn /= [x vt]].
    - exact: [tuple].
    - exact: [tuple of x :: (ihn vt)].
  Defined.

  Definition vt := nosimpl vt_def.

  Prenex Implicits vt tv.

  Lemma vt_cons n x (xs : V n T) :
    vt (vcons x xs) = [tuple of x :: vt xs].
  Proof. by []. Qed.

  Lemma tvK n : cancel (@vt n) tv.
  Proof.
    elim: n => [ [] | n ih [x v] ].
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
  Definition vt' n (v : V n T) : n.-tuple T := Tuple (vtSP v).

  Lemma vt'_cons n x (xs : V n T) :
    vt' (vcons x xs) = [tuple of x :: vt' xs].
  Proof. exact: val_inj. Qed.

End VecTuple.

Module FinVector.
Section FinVector.
Variables (n : nat) (T : finType).

(* Generate all the vectors of size n from T *)
Definition enum_def : seq (V n T) :=
  seq.map (@tv T n) (FinTuple.enum n T).

Definition enum := nosimpl enum_def.

Lemma eq_tv_vt (v : V n T) : [pred x | tv x == v] =1 [pred x | x == vt v].
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
Canonical vector_finType  := Eval hnf in FinType (V n T) vector_finMixin.
Canonical vector_subFinType := Eval hnf in [subFinType of V n T].

End UseFinVector.

Section IndVec.

  (* TODO: Define a principle to prove things over t A n, but in such
     a way that the subcases are handled over standard lists plus a
     size predicate about them *)

  Definition kk (A : Type) m t (x : A) (H : size t == m) : size (x :: t) == m.+1.
  Proof. by []. Qed.

  Definition vec_rect :
    forall (A : Type) (P : forall n : nat, V n A -> Type),
      (P 0 (vnil)) ->
      (forall (h : A) (n : nat) (t : seq A) (H : size t == n),
         P n (tvS H) -> P n.+1 (tvS (kk h H))) ->
    forall (n : nat) (t : V n A), P n t.
  Proof.
  move=> T P Hnil Hcons n.
  elim: n => [|n ihn] [//=] x t.
  rewrite -[t]tvSK.
  move: (Hcons x n t (vtSP t)).
  by rewrite (eq_irrelevance (kk x _) (vtSP _)); apply.
  Qed.

(*
  Definition vec_rect :
    forall (A : Type) (P : forall n : nat, t A n -> Type),
      (P 0 (nil A) ->
      (forall (h : A) (n : nat) (t : t A n), P n t -> P n.+1 (cons A h n t)) ->
    forall (n : nat) (t : t A n), P n t


*)
