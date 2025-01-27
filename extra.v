From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "''P_' i" (at level 8, i at level 2, format "''P_' i").
Reserved Notation "Γ ⊢ M : A"
  (format "Γ  ⊢  M  :  A", at level 100, M, A at next level).

Notation "x ∈ A" := (x \in A) (at level 70).
Notation "x ∉ A" := (x \notin A) (at level 70).
Notation "[ 'ord' i ]" := (@Ordinal _ i _)
  (format "[ 'ord'  i ]", at level 0).

Lemma mem_nthE [T : eqType] (x0 : T) [s : seq T] n :
  nth x0 s n ∈ s = ((n >= size s) ==> (x0 ∈ s)).
Proof.
apply/idP/idP; first by case: ltnP => // ?; rewrite nth_default.
by case: ltnP => //= ns x0s; [rewrite mem_nth|rewrite nth_default].
Qed.

Notation "[-->]" := (ltac:(let x := fresh "x" in (
  intro x; match goal with x : ?l = ?r |- _ => subst l end)))
  (only parsing): ssripat_scope.

Lemma all_memP (T : eqType) (r s : seq T) :
  reflect {subset s <= r} (all [in r] s).
Proof. by apply: (iffP allP) => rs + /rs. Defined.

Lemma tnth_in_tuple_map T T' (f : T -> T') l
    (i j : 'I__) : i = j :> nat ->
  tnth (in_tuple (map f l)) i = f (tnth (in_tuple l) j).
Proof.
move=> eqij; rewrite /tnth /=.
set x := tnth_default _ _; set x' := tnth_default _ _.
by rewrite (nth_map x')/= ?eqij//=; congr (f (nth _ _ _)).
Qed.

Lemma subset_cons2 (T : eqType) (x : T) s s' :
  {subset s <= s'} -> {subset x :: s <= x :: s'}.
Proof.
by move=> ss' y; rewrite !in_cons => /orP[->//|/ss'->]; rewrite orbT.
Qed.

Lemma subset_cons (T : eqType) (x : T) (s : seq T) s' :
  {subset s <= s'} -> {subset s <= x :: s'}.
Proof. by move=> ss' y; rewrite !in_cons => /ss'-> /[!orbT]. Qed.

Lemma subset_memP {T : eqType} (r s : seq T) :
  {subset r <= s} -> {r' | subseq r' s & r =i r'}.
Proof.
move=> rs; exists (filter [in r] s); first by rewrite filter_subseq.
by move=> x; rewrite mem_filter andb_idr//; apply: rs.
Qed.

Definition tact {T n} (σ : 'S_n) (t : n.-tuple T) : list T :=
  [tuple tnth t (σ i) | i < n].

Lemma perm_tact {T : eqType} {n} (σ : 'S_n) (t : n.-tuple T) :
  perm_eq (tact σ t) t.
Proof. by apply/tuple_permP; exists σ. Qed.

Lemma tact1 {T : eqType} {n} (t : n.-tuple T) : tact 1 t = t.
Proof.
congr tval; apply/eq_from_tnth => i.
by rewrite !tnth_map /= permE /= !tnth_ord_tuple.
Qed.

Lemma tactM {T : eqType} {n} (σ τ : 'S_n) (t : n.-tuple T) :
  tact (σ * τ) t = tact σ (tact τ t).
Proof.
congr tval; apply/eq_from_tnth => i.
by rewrite !tnth_map /= permE /= !tnth_ord_tuple.
Qed.

Lemma tactK {T : eqType} {n} (σ τ : 'S_n) (t : n.-tuple T) :
  tact σ^-1 (tact σ t) = t.
Proof. by rewrite -tactM mulVg tact1. Qed.

Lemma tact_subproof {T n} (σ : 'S_n) (t : n.-tuple T) :
   size (tact σ t) == n.
Proof. by rewrite size_tuple. Qed.

Canonical tact_tuple {T n} (σ : 'S_n) (t : n.-tuple T) :=
  Tuple (tact_subproof σ t).

Lemma tactE {T n} (σ : 'S_n) (t : n.-tuple T) :
  tact_tuple σ t = [tuple tnth t (σ i) | i < n] :> n.-tuple T.
Proof. exact/val_inj. Qed.

Lemma tnth_in_tuple n T (t : n.-tuple T) i :
   tnth (in_tuple t) i = tnth t (cast_ord (size_tuple _) i).
Proof. exact/set_nth_default. Qed.

Lemma in_tuple_tuple n T (t : n.-tuple T) :
  in_tuple t = tcast (esym (size_tuple _)) t.
Proof.
by apply/eq_from_tnth=> i; rewrite tnth_in_tuple/= tcastE esymK.
Qed.

Lemma tnth_tact {T n} (σ : 'S_n) (t : n.-tuple T) i :
  tnth (tact σ t) i = tnth t (σ i).
Proof. by rewrite tactE tnth_mktuple. Qed.

Lemma tact_lift0 {T n} (σ : 'S_n) x (t : n.-tuple T) :
  tact (lift0_perm σ) (x :: t) = x :: tact σ t :> n.+1.-tuple T.
Proof.
apply/eq_from_tnth => i; rewrite tnth_tact.
have [_/[!ord1]->|k {i}->] := @split_ordP 1 n i.
  by rewrite !lshift0/= lift0_perm0.
by rewrite !rshift1 lift0_perm_lift !tnthS tnth_tact.
Qed.

Lemma tval_tact_lift0 {T n} (σ : 'S_n) x (t : n.-tuple T) :
  tact (lift0_perm σ) (x :: t) = x :: tact σ t.
Proof. by have /(congr1 val) := tact_lift0 σ x t. Qed.

Lemma in_tuple_cons T x (t : list T) :
   in_tuple (x :: t) = x :: in_tuple t.
Proof.
have -> : t = in_tuple t by [].
apply/eq_from_tnth => i; rewrite tnth_in_tuple /=.
by apply/set_nth_default => /=.
Qed.

Lemma in_tupleP {T : Type} (P : list T -> Type) :
  (forall n (t : n.-tuple T), P t) -> forall l, P l.
Proof. by move=> + l => /(_ _ (in_tuple l)). Qed.

Lemma tactP {T : eqType} {n : nat} {s : seq T} {t : n.-tuple T} :
  reflect (exists σ : {perm 'I_n}, s = tact σ t) (perm_eq s t).
Proof. exact: tuple_permP. Qed.

HB.mixin Record hasFresh X of Equality X := {
  fresh : seq X -> X;
  freshP : forall s, fresh s ∉ s
}.
#[short(type="infiniteType")]
HB.structure Definition Infinite := {X of Choice X & hasFresh X}.