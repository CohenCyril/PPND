From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
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

Lemma derivable_admissible r : derivable r -> admissible r.
Proof.
unfold derivable, admissible; elim => //=.
- move=> s; elim: (premises r) => //= s0 pr IHpr.
  rewrite in_cons.
  case: eqVneq => [->|].
    by move=> _; by case.
  move=> /= _.
  move=> spr.
  case=> _.
  by apply: IHpr.
- by move=> Γ A i eqA _; apply: (Ax _ _ _ i).
Admitted.

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

Lemma weakening Γ A B : derivation [::] (Γ ⊢ B) -> derivation [::] (A :: Γ ⊢ B).
Proof.
set s := (Γ ⊢ B).
rewrite -[Γ]/(hypotheses s) -[B]/(thesis s).
elim => //=.
- move=> {s}Γ {}B i eqB.
  apply: (Ax _ _ _ [ord i.+1]).
    by rewrite /= ltnS//.
  move=> Hi.
  rewrite /tnth/=.
  rewrite in_tuple_cons/=.
  by rewrite -(tnth_nth _ (in_tuple Γ)).
- move=> {s}Γ {}B _ Hbot.
  by apply: BotE.
-
Admitted.

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

