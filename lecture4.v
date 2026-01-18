From HB Require Import structures.
From mathcomp Require Import all_boot all_order.
From deriving Require Import deriving.
From ND Require Import extra.


Declare Scope NJ_scope.
Delimit Scope NJ_scope with NJ.
Local Open Scope NJ_scope.

Module bin.
Inductive op := And | Or | Imply.
End bin.

Definition op_indDef := [indDef for bin.op_rect].
Canonical op_indType := IndType bin.op op_indDef.
Definition op_hasEqDec := [derive hasDecEq for bin.op].
HB.instance Definition _ := op_hasEqDec.

Inductive formula : Type :=
| Var : nat -> formula
| Bot : formula
| BinOp : bin.op -> formula -> formula -> formula.

Definition formula_indDef := [indDef for formula_rect].
Canonical formula_indType := IndType formula formula_indDef.
Definition formula_hasEqDec := [derive hasDecEq for formula].
HB.instance Definition _ := formula_hasEqDec.

Notation Imply := (BinOp bin.Imply).
Notation Or := (BinOp bin.Or).
Notation And := (BinOp bin.And).

Notation "A ⇒ B" := (Imply A B) (right associativity, at level 99) : NJ_scope.
Notation "A ∧ B" := (And A B) (right associativity, at level 80) : NJ_scope.
Notation "A ∨ B" := (Or A B) (right associativity, at level 85) : NJ_scope.
Notation "⊥" := Bot : NJ_scope.
Notation "¬ A" := (A ⇒ ⊥) (at level 75) : NJ_scope.
Notation Top := (¬ Bot).
Notation "⊤" := Top : NJ_scope.
Notation Neg := (fun x => Imply x Bot).
Notation "'P_ n" := (Var n) : NJ_scope.

Record sequent := Sequent {
  hypotheses : list formula;
  thesis : formula;
}.
Scheme sequent_rect := Induction for sequent Sort Type.
Definition sequent_indDef := [indDef for sequent_rect].
Canonical sequent_indType := IndType sequent sequent_indDef.
Definition sequent_hasEqDec := [derive hasDecEq for sequent].
HB.instance Definition _ := sequent_hasEqDec.

Record rule := Rule {
  premises : list sequent;
  conclusion : sequent  
}.
Scheme rule_rect := Induction for rule Sort Type.
Definition rule_indDef := [indDef for rule_rect].
Canonical rule_indType := IndType rule rule_indDef.
Definition rule_hasEqDec := [derive hasDecEq for rule].
HB.instance Definition _ := rule_hasEqDec.

Notation "Γ ⊢ A" := (Sequent Γ A) (at level 100) : NJ_scope.

Set Uniform Inductive Parameters.

Inductive derivation (premises : list sequent) : sequent -> Type :=
| Prem s : s ∈ premises -> derivation s
| Ax (Γ : list formula) (A : formula) (i : 'I_(size Γ)) :
   tnth (in_tuple Γ) i = A -> derivation (Γ ⊢ A)
| BotE Γ A : derivation (Γ ⊢ ⊥) -> derivation (Γ ⊢ A)
| ImplyI Γ A B : derivation (A :: Γ ⊢ B) -> derivation (Γ ⊢ A ⇒ B)
| ImplyE Γ A B : derivation (Γ ⊢ A ⇒ B) -> derivation (Γ ⊢ A) ->
                 derivation (Γ ⊢ B)
| AndI Γ A B : derivation (Γ ⊢ A) -> derivation (Γ ⊢ B) ->
               derivation (Γ ⊢ A ∧ B)
| AndE1 Γ A B : derivation (Γ ⊢ A ∧ B) -> derivation (Γ ⊢ A)
| AndE2 Γ A B : derivation (Γ ⊢ A ∧ B) -> derivation (Γ ⊢ B)
| OrI1 Γ A B : derivation (Γ ⊢ A) -> derivation (Γ ⊢ A ∨ B)
| OrI2 Γ A B : derivation (Γ ⊢ B) -> derivation (Γ ⊢ A ∨ B)
| OrE Γ A B C: derivation (Γ ⊢ A ∨ B) -> derivation (A :: Γ ⊢ C) ->
            derivation (B :: Γ ⊢ C) -> derivation (Γ ⊢ C).

Definition derivable (r : rule) := derivation (premises r) (conclusion r).

Definition derivations (ls : list sequent) :=
   foldr (fun s d => (derivation [::] s * d)%type) unit ls.

Definition admissible (r : rule) := derivations (premises r) ->
    derivation [::] (conclusion r).

Arguments Ax {premises Γ A}.

Definition AxN {premises Γ A} (i : nat) : onth Γ i = Some A ->
  derivation premises (Γ ⊢ A).
Proof.
move=> nthA; have iΓ : i < size Γ by rewrite -onthTE nthA.
exact/(Ax (Ordinal iΓ))/tnth_onth.
Defined.

Lemma derivable_admissible r : derivable r -> admissible r.
Proof.
unfold derivable, admissible; elim => //=.
- move=> s; elim: (premises r) => //= s0 pr IHpr; rewrite in_cons.
  by case: eqVneq => [->|]; tauto.
- by move=> Γ A i eqA _; apply: (Ax i).
- by firstorder using BotE.
- by firstorder using ImplyI.
- by firstorder using ImplyE.
- by firstorder using AndI.
- by move=> Γ A B; have := @AndE1 [::] Γ A B; tauto.
- by move=> Γ A B; have := @AndE2 [::] Γ A B; tauto.
- by firstorder using OrI1.
- by firstorder using OrI2.
- by move=> Γ A B C; have := @OrE [::] Γ A B C; tauto.
Qed.
  
Definition reversible (r : rule) := 
  derivation [::] (conclusion r) -> derivations (premises r).

Definition ImplyI_rule Γ A B : rule := Rule [:: A :: Γ ⊢ B] (Γ ⊢ A ⇒ B).

Lemma ImplyI_derivable Γ A B : derivable (ImplyI_rule Γ A B).
Proof.
rewrite /derivable/=.
apply: ImplyI.
apply: Prem.
by rewrite mem_head.
Qed.

(* Lemma exchange Γ A B C : *)
(*   derivation [::] (B :: A :: Γ ⊢ C) -> derivation [::] (A :: B :: Γ ⊢ C). *)
(* Proof. *)
(* set s := (_ ⊢ _). *)
(* have -> : B = nth (Var 0) (hypotheses s) 0 by []. *)
(* have -> : A = nth (Var 0) (hypotheses s) 1 by []. *)
(* have -> : Γ = behead (behead (hypotheses s)) by []. *)
(* have -> : C = thesis s by []. *)
(* have/[swap]: size (hypotheses s) > 1 by []. *)
(* elim => //= {Γ A B C s} - [|A [|B Γ]] //=. *)
(* - move=> D [[<-]|[[<-]|i nthD]]//= _. *)
(*   + exact: (Ax _ _ _ 1). *)
(*   + exact: (Ax _ _ _ 0). *)
(*   + exact: (Ax _ _ _ i.+2). *)
(* - by firstorder using BotE. *)
(* - move=> C D. /by firstorder using ImplyI. *)
  
(* move=> d. *)
(* elim. *)

Lemma sig_eq2W (T : choiceType) (vT vT' : eqType)
  (lhs rhs : T -> vT) (lhs' rhs' : T -> vT') :
    (exists2 x : T, lhs x = rhs x & lhs' x = rhs' x) ->
    {x : T | lhs x = rhs x & lhs' x = rhs' x}.
Proof.
move=> e; suff [x /eqP]: {x : T | lhs x == rhs x & lhs' x = rhs' x} by exists x.
by apply: sig2_eqW; case: e => x /eqP; exists x.
Qed.

Definition index_mask (m : seq bool) i :=
  nth (size m) (mask m (iota 0 (size m))) i.

Lemma map_nth {T1 T2 : Type} (f : T1 -> T2) x (n : nat) (s : seq T1) :
  f (nth x s n) = nth (f x) [seq f i | i <- s] n.
Proof. by elim: n s => [|n IHn] [|y s] /=. Qed.
                                            
Lemma nth_cons [T : Type] (x0 x : T) (s2 : seq T) (n : nat) :
  nth x0 (x :: s2) n = (if n == 0 then x else nth x0 s2 (n.-1)).
Proof. by rewrite -cat1s nth_cat/=; case: n => //= n; rewrite subn1. Qed.

Lemma nth_index_mask {T} (m : seq bool) x0 (s : seq T) : size m >= size s ->
  forall i, nth x0 (mask m s) i = nth x0 s (index_mask m i).
Proof.
rewrite /index_mask => sm i.
by elim: m s sm i => [|[] m IHm]//= [|x s]//= sm [|i];
   rewrite ?nth_nil ?(iotaDl 1)//= -map_mask -map_nth/= IHm.
Qed.

  
Lemma weakening Γ Γ' B : subseq Γ Γ' ->
  derivation [::] (Γ ⊢ B) -> derivation [::] (Γ' ⊢ B).
Proof.
set s := (Γ ⊢ B); rewrite -[B]/(thesis s) -[Γ]/(hypotheses s).
move: s => s sΓ' ds; elim: ds Γ' sΓ' => //= {B s}Γ.
- move=> A i <- Γ' /subseqP/sig_eq2W/=[m sm Γeq].
  apply: (AxN (index_mask m i)).
  rewrite onthE -nth_index_mask ?size_map -?sm//.
  by rewrite -map_mask -Γeq -onthE; apply/(tnth_onth _ (in_tuple Γ)).
- by move=> A d d' Γ' ΓΓ'; apply/BotE/d'.
- by move=> A B d d' Γ' ΓΓ'; apply/ImplyI/d'; rewrite /= eqxx.
- by move=> A B d1 d1' d2 d2' Γ' ΓΓ'; apply/ImplyE/d2'/ΓΓ'/d1'.
- by move=> A B d1 d1' d2 d2' Γ' ΓΓ'; apply/AndI/d2'/ΓΓ'/d1'.
- by move=> A B d d' Γ' ΓΓ'; apply/AndE1/d'.
- by move=> A B d d' Γ' ΓΓ'; apply/AndE2/d'.
- by move=> A B d d' Γ' ΓΓ'; apply/OrI1/d'.
- by move=> A B d d' Γ' ΓΓ'; apply/OrI2/d'.
- move=> A B C d1 d1' d2 d2' d3 d3' Γ' ΓΓ'.
  by apply: (OrE _ _ _ _ _ (d1' _ _) (d2' _ _) (d3' _ _)) => //=; rewrite eqxx.
Qed.
  
Lemma ImplyI_reversible Γ A B : reversible (ImplyI_rule Γ A B).
Proof.
rewrite /reversible/=.
move=> dAB.
split => //.
apply: (ImplyE _ _ A); last first.
  by apply: (Ax _ _ _ [ord 0]) => /=.
by apply: weakening.
Qed.

Fixpoint subst_formula (ρ : list formula) (A : formula) :=
match A with
| Var i => nth (Var (i - size ρ)) ρ i
| Bot => Bot
| BinOp op A B => BinOp op (subst_formula ρ A) (subst_formula ρ B)
end.

Definition subst_sequent ρ s :=
  Sequent (map (subst_formula ρ) (hypotheses s)) (subst_formula ρ (thesis s)).

Lemma subst_sequentE Γ A ρ :
  subst_sequent ρ (Γ ⊢ A) = (map (subst_formula ρ) Γ ⊢ subst_formula ρ A).
Proof. by []. Qed.

Lemma subst_derivation ρ prem s : derivation prem s ->
   derivation (map (subst_sequent ρ) prem) (subst_sequent ρ s).
Proof.
elim.
- admit.
- move=> Γ A i eqA /=.
  apply: (Ax _ _ _ [ord i]). 
    by rewrite size_map/=.
  move=> Hi/=.

  rewrite /tnth/=.
  rewrite (nth_map A)//.
  rewrite -(tnth_nth _ (in_tuple Γ)).
  by rewrite eqA.
- by move=> Γ A _; apply: BotE.
Admitted.

