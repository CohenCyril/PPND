From HB Require Import structures.
From mathcomp Require Import all_boot all_order fingroup perm zmodp zify.
From deriving Require Import deriving.
From ND Require Import extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Uniform Inductive Parameters.

Declare Scope NJ_scope.
Delimit Scope NJ_scope with NJ.
Local Open Scope NJ_scope.

(***********)
(* Formula *)
(***********)

(* First we define binary operators in a scope *)
Module Op.
Inductive bin : Type := Or | And | Imply.
End Op.

(* The following instructions endow `Op.bin`              *)
(* with equality, choice and countability structures.     *)
(* This is particularily useful when programming with it. *)
Definition binOp_indDef := [indDef for Op.bin_rect].
Canonical binOp_indType := IndType Op.bin binOp_indDef.
Definition binOp_hasDecEq := [derive hasDecEq for Op.bin].
HB.instance Definition _ := binOp_hasDecEq.
Definition binOp_choice := [derive hasChoice for Op.bin].
HB.instance Definition _ := binOp_choice.
Definition binOp_countable := [derive isCountable for Op.bin].
HB.instance Definition _ := binOp_countable.

(* Now we define formulae. *)
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

(* Shortcut notations *)
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

(* We define the size of a formula, in case we need to perform *)
(* non structural induction.                                   *)
Fixpoint size_formula (A : formula) : nat :=
  match A with
    | Var _ => 1
    | Bot => 1
    | BinOp op A B => size_formula A + size_formula B
  end. 

Lemma size_formula_gt0 (A : formula) : size_formula A > 0.
Proof. by elim: A => [n //| // |op A A_gt0 B B_gt0] /=; lia. Qed.
Hint Resolve size_formula_gt0 : core.

(************)
(* Sequents *)
(************)

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
Notation "⊢ B" := (Sequent [::] B) (at level 100) : NJ_scope.
Coercion formula_to_sequent := Sequent [::].
Arguments formula_to_sequent /.

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
Arguments ImplyE [_ _] A.
Arguments AndE1 [_ _ A] B.
Arguments AndE2 [_ _] A [B].
Arguments OrE [_ _] A B [C].

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

Coercion single_sequent (f : sequent) := [:: f].
Notation "p --------------------- c" := (Rule p c)
  (format "'[v   ' '//' '[' p ']' '//' --------------------- '//' '[' c ']' '//' ']'",
   at level 150) : NJ_scope.
Coercion JustConcl (s : sequent) : rule := Rule [::] s.

Module Rule.

Definition Ax Γ i : rule := Γ ⊢ tnth (in_tuple Γ) i.
Definition TopI Γ : rule := Γ ⊢ ⊤.
Definition BotE Γ A := Rule (Γ ⊢ ⊥) (Γ ⊢ A).
Definition NegI Γ A := Rule (A :: Γ ⊢ ⊥) (Γ ⊢ ¬ A).
Definition NegE Γ A := Rule [:: Γ ⊢ ¬ A ; Γ ⊢ A] (Γ ⊢ ⊥).
Definition AndI Γ A B := Rule [:: Γ ⊢ A ; Γ ⊢ B] (Γ ⊢ A ∧ B).
Definition AndE1 Γ A B := Rule (Γ ⊢ A ∧ B) (Γ ⊢ A).
Definition AndE2 Γ A B := Rule (Γ ⊢ A ∧ B) (Γ ⊢ B).
Definition OrI1 Γ A B := Rule (Γ ⊢ A) (Γ ⊢ A ∨ B).
Definition OrI2 Γ A B := Rule (Γ ⊢ B) (Γ ⊢ A ∨ B).
Definition OrE Γ A B C := Rule [:: Γ ⊢ A ∨ B ; A :: Γ ⊢ C; B :: Γ ⊢ C] (Γ ⊢ C).
Definition ImplyI Γ A B := Rule (A :: Γ ⊢ B) (Γ ⊢ A ⇒ B).
Definition ImplyE Γ A B := Rule [:: Γ ⊢ A; Γ ⊢ A ⇒ B] (Γ ⊢ B).

End Rule.

Definition derivable (r : rule) := derivation (premises r) (conclusion r).
Definition provable s := derivation [::] s.

(* casting from derivation ps c to derivable (Rule ps c) *)
Coercion derivable_of_derivation ps c (d : derivation ps c) :
   derivable (Rule ps c) := d.

Definition admissible (r : rule) :=
  (forall s, s \in premises r -> provable s) -> provable (conclusion r).

(* Q1. very easy *)
Lemma derivable_admissible (r : rule) :
  derivable r -> admissible r.
Proof.
rewrite /derivable /admissible/=.
move=> d.
elim: d => //=.
- by intros s sP Ps; have := Ps s sP.
- by move=> ? ? i *; apply: (Ax i).
- move=> Γ A d0 IHd0 Ps.
  apply: (BotE A).
  by apply: IHd0.
- move=> Γ A B d0 IHd0 Ps.
  apply: ImplyI.
  by apply: IHd0.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
- move=> Γ A B C d0 IHd0 d1 IHd1 d2 IHd2 Ps.
  apply: OrE.
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

(* Q3. medium *)
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
  by apply/tnth_onth; rewrite Some_tnth.
- by move=> {s B}Γ B _; apply: BotE.
Admitted.

(* Q2. easy (using weakening_admissible) *)
Lemma ImplyI_reversible Γ A B : reversible (Rule.ImplyI Γ A B).
Proof.
Abort.

Definition exchange Γ A B Δ C :=
  Rule [:: Γ ++ A :: B :: Δ ⊢ C] (Γ ++ B :: A :: Δ ⊢ C).

(* Q4. difficult *)
Lemma exchange_admissible Γ A B Δ C :
  admissible (exchange Γ A B Δ C).
Proof. Abort.

(* Q5. extremely difficult *)
Lemma weakening_nonderivable :
  (forall Γ A B, derivable (weakening Γ A B)) -> provable ⊥.
Proof. Abort.  
