From HB Require Import structures.
From mathcomp Require Import all_boot all_order fingroup perm zmodp.
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

Definition AxP {premises Γ A} (i : nat) (ilt : i < size Γ):
   tnth (in_tuple Γ) (Ordinal ilt) = A -> derivation premises (Γ ⊢ A).
Proof. exact: Ax. Qed.

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

Lemma exchange Γ Γ' A : perm_eq Γ Γ' ->
  derivation [::] (Γ ⊢ A) -> derivation [::] (Γ' ⊢ A).
Proof.
set s := (Γ ⊢ A); rewrite -[A]/(thesis s) -[Γ]/(hypotheses s) => /[swap] d.
elim: d Γ' => //= => {A s}Γ.
- move=> A i <- Γ' /[1!perm_sym] /(@tactP _ _ _ (in_tuple _))/sig_eqW[/= σ ->].
  apply/(AxN (σ^-1%g i))/tnth_onthP; rewrite tnth_tact/=; congr (tnth _).
  by apply/val_inj; rewrite ordE/= permKV.
- by move=> A d + {}Γ' ΓΓ' => /(_ Γ' ΓΓ'); apply/BotE.
- by move=> A N d d' Γ' ΓΓ; apply/ImplyI/d'; rewrite perm_cons.
- by move=>  A B d1 d1' d2 d2' Γ' ΓΓ'; apply/ImplyE/d2'/ΓΓ'/d1'.
- by move=>  A B d1 d1' d2 d2' Γ' ΓΓ'; apply/AndI/d2'/ΓΓ'/d1'.
- by move=> A N d d' Γ' ΓΓ; apply/AndE1/d'.
- by move=> A N d d' Γ' ΓΓ; apply/AndE2/d'.
- by move=> A N d d' Γ' ΓΓ; apply/OrI1/d'.
- by move=> A N d d' Γ' ΓΓ; apply/OrI2/d'.
- move=> A B C d1 d1' d2 d2' d3 d3' Γ' ΓΓ'; apply/(OrE _ _ A B).
  - exact: d1'.
  - by apply: d2'; rewrite perm_cons.
  - by apply: d3'; rewrite perm_cons.
Qed. 
  
Lemma exchange2 Γ Δ A B C :
  derivation [::] (Γ ++ A :: B :: Δ ⊢ C) -> derivation [::] (Γ ++ B :: A :: Δ ⊢ C).
Proof.
apply/exchange/perm_cat => //.
by rewrite -![_ :: (_ :: _)]cat1s -![_ :: Δ]cat1s perm_catCA.
Qed.
  
Lemma weakening Γ Γ' A : subseq Γ Γ' ->
  derivation [::] (Γ ⊢ A) -> derivation [::] (Γ' ⊢ A).
Proof.
set s := (Γ ⊢ A); rewrite -[A]/(thesis s) -[Γ]/(hypotheses s).
move: s => s sΓ' ds; elim: ds Γ' sΓ' => //= {A s}Γ.
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

Lemma weakening1 Γ A B : derivation [::] (Γ ⊢ B) -> derivation [::] (A :: Γ ⊢ B).
Proof. by apply: weakening; rewrite subseq_cons. Qed.
  
Lemma ImplyI_reversible Γ A B : reversible (ImplyI_rule Γ A B).
Proof.
rewrite /reversible/=.
move=> dAB.
split => //.
apply: (ImplyE _ _ A); last first.
  exact: (Ax [ord 0]).
exact: weakening1.
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
- by move=> /= {}s sprem; apply: Prem; rewrite map_f.
- move=> Γ A i eqA /=.
  apply: (Ax [ord i]). 
    by rewrite size_map/=.
  move=> Hi/=.
  rewrite /tnth/=.
  rewrite (nth_map A)//.
  rewrite -(tnth_nth _ (in_tuple Γ)).
  by rewrite eqA.
- by move=> Γ A _; apply: BotE.
- by move=> Γ A B d d' /=; apply: ImplyI.
- by move=> Γ A B d1 d1' d2 d2'; apply: ImplyE d2'.
- by move=> Γ A B d1 d1' d2 d2'; apply: AndI d2'.
- by move=> Γ A B d d' /=; apply: AndE1 d'.
- by move=> Γ A B d d' /=; apply: AndE2 d'.
- by move=> Γ A B d d' /=; apply: OrI1 d'.
- by move=> Γ A B d d' /=; apply: OrI2 d'.
- by move=> Γ A B C d1 d1' d2 d2' d3 d3'; apply: OrE d2' d3'.
Qed.  
