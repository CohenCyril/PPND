From HB Require Import structures.
From mathcomp Require Import all_boot all_order fingroup perm zmodp zify.
From deriving Require Import deriving.
From ND Require Import extra.

Declare Scope NJ_scope.
Delimit Scope NJ_scope with NJ.
Local Open Scope NJ_scope.

(* Formula *)

Module Op.
Inductive bin : Type := Or | And | Imply.
End Op.

Definition binOp_indDef := [indDef for Op.bin_rect].
Canonical binOp_indType := IndType Op.bin binOp_indDef.

Definition binOp_hasDecEq := [derive hasDecEq for Op.bin].
HB.instance Definition _ := binOp_hasDecEq.
Definition binOp_choice := [derive hasChoice for Op.bin].
HB.instance Definition _ := binOp_choice.
Definition binOp_countable := [derive isCountable for Op.bin].
HB.instance Definition _ := binOp_countable.

Inductive formula :=
  | Var of nat
  | Bot 
  | BinOp of Op.bin & formula & formula.

Definition formula_indDef := [indDef for formula_rect].
Canonical formula_indType := IndType formula formula_indDef.

Definition formula_hasDecEq := [derive hasDecEq for formula].
HB.instance Definition _ := formula_hasDecEq.
Definition formula_choice := [derive hasChoice for formula].
HB.instance Definition _ := formula_choice.
Definition formula_countable := [derive isCountable for formula].
HB.instance Definition _ := formula_countable.

Notation Or := (BinOp Op.Or).
Notation And := (BinOp Op.And).
Notation Imply := (BinOp Op.Imply).

Notation "A ⇒ B" := (Imply A B) (right associativity, at level 99) : NJ_scope.
Notation "A ∧ B" := (And A B) (right associativity, at level 80) : NJ_scope.
Notation "A ∨ B" := (Or A B) (right associativity, at level 85) : NJ_scope.
Notation "⊥" := Bot : NJ_scope.
Notation "¬ A" := (A ⇒ ⊥) (at level 75) : NJ_scope.
Notation Top := (¬ Bot).
Notation "⊤" := Top : NJ_scope.
Notation Neg := (fun x => Imply x Bot).
Notation "'P_ n" := (Var n) : NJ_scope.

Fixpoint size_formula (A : formula) : nat :=
  match A with
    | Var _ => 1
    | Bot => 1
    | BinOp op A B => size_formula A + size_formula B
  end. 

Lemma size_formula_gt0 (A : formula) : size_formula A > 0.
Proof. by elim: A => [n //| // |op A A_gt0 B B_gt0] /=; lia. Qed.
Hint Resolve size_formula_gt0 : core.

(* sequent *)
Record sequent := Sequent {
  hypotheses : list formula;
  thesis : formula; 
}.
Bind Scope NJ_scope with sequent.

Scheme sequent_rect := Induction for sequent Sort Type.
Definition sequent_indDef := [indDef for sequent_rect].
Canonical sequent_indType := IndType sequent sequent_indDef.

Definition sequent_hasDecEq := [derive hasDecEq for sequent].
HB.instance Definition _ := sequent_hasDecEq.
Definition sequent_choice := [derive hasChoice for sequent].
HB.instance Definition _ := sequent_choice.
Definition sequent_countable := [derive isCountable for sequent].
HB.instance Definition _ := sequent_countable.

Coercion singlef (f : formula) := [:: f].
Notation "Γ ⊢ A" := (Sequent Γ A) (at level 100) : NJ_scope.

Set Uniform Inductive Parameters.

(* derivation *)

Inductive derivation (prem : list sequent) : sequent -> Type :=
| Prem s : s \in prem -> derivation s 
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

Arguments Ax {_ _ _}.

Definition AxP prem (Γ : list formula) (A : formula) (i : nat)
    (ilt : i < size Γ) :
  tnth (in_tuple Γ) (Ordinal ilt) = A -> derivation prem (Γ ⊢ A).
Proof. exact: Ax. Defined.

Arguments AxP {_ _ _}.

Lemma ex1 : derivation [::] ([:: Var 0; Var 1] ⊢ Var 0).
Proof.
by apply: (Ax [ord 0]).
Qed.

(* rules *)
Record rule := Rule {
  premises : list sequent;
  conclusion : sequent;
}.
Scheme rule_rect := Induction for sequent Sort Type.
Definition rule_indDef := [indDef for sequent_rect].
Canonical rule_indType := IndType sequent sequent_indDef.

Definition rule_hasDecEq := [derive hasDecEq for sequent].
HB.instance Definition _ := rule_hasDecEq.
Definition rule_choice := [derive hasChoice for sequent].
HB.instance Definition _ := rule_choice.
Definition rule_countable := [derive isCountable for sequent].
HB.instance Definition _ := rule_countable.

Definition derivable (r : rule) :=
  derivation (premises r) (conclusion r).
Definition provable s := derivation [::] s.

Definition admissible (r : rule) :=
  (forall s, s \in premises r -> provable s) -> provable (conclusion r).

Lemma derivable_admissible (r : rule) :
  derivable r -> admissible r.
Proof.
rewrite /derivable /admissible/=.
move=> d.
elim: d => //=.
- by intros s sP Ps; have := Ps s sP.
- by move=> ? ? i *; apply: (Ax i).
- move=> Γ A d0 IHd0 Ps.
  apply: (BotE _ Γ A).
  by apply: IHd0.
- move=> Γ A B d0 IHd0 Ps.
  apply: (ImplyI _ Γ A B).
  by apply: IHd0.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
- move=> Γ A B C d0 IHd0 d1 IHd1 d2 IHd2 Ps.
  apply: (OrE _ Γ A B C).
  - by apply: IHd0.
  - by apply: IHd1.
  - by apply: IHd2.
Admitted.

Definition reversible r :=
  (admissible r *
    (forall p, p ∈ premises r ->
          admissible (Rule [:: conclusion r] (p))))%type.


Definition weakening Γ A B := Rule [:: Γ ⊢ B] (A :: Γ ⊢ B).

Definition gen_weakening Γ Θ A (ΓΘ : subseq Θ Γ) :=
  Rule [:: Θ ⊢ A] (Γ ⊢ A).

(* Definition exchange Γ A B Δ C := *)
(*   Rule [:: Γ ++ A :: B :: Δ ⊢ C] (Γ ++ B :: A :: Δ ⊢ C). *)

(* Lemma exchange_admissible Γ A B Δ C : *)
(*   admissible (exchange Γ A B Δ C). *)
(* Proof. Admitted. *)

Lemma weakening_admissible Γ A B : admissible (weakening Γ A B).
Proof.
move=> /= sP; have {sP} := sP _ (mem_head _ _).
set s := (Γ ⊢ B).
change Γ with (hypotheses s).
change B with (thesis s).
elim=> //=.
- move=> {s B}Γ B i <-.
  apply: (AxP i.+1); first by rewrite /= ltnS.
  move=> ilt //=.
  apply/tnth_onth => //=.
  by apply/(tnth_onthP _ (in_tuple Γ)); rewrite ordE.
- by move=> {s B}Γ B _; apply: BotE.
Admitted.
