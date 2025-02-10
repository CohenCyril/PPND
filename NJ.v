From HB Require Import structures.
From Coq Require Import String.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From deriving Require Import deriving.
From mathcomp Require Import zify lra ring.

From ND Require Import extra.

Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
#[global] Set Uniform Inductive Parameters.

Declare Scope NJ_scope.
Delimit Scope NJ_scope with NJ.
Local Open Scope NJ_scope.

Module NJ.

(************)
(* Formulae *)
(************)

Module Op.
Inductive bin : Type := Or | And | Imply.
End Op.

Definition binOp_indDef := [indDef for Op.bin_rect].
Canonical binOp_indType := IndType Op.bin binOp_indDef.

Definition binOp_hasDecEq := [derive hasDecEq for Op.bin].
HB.instance Definition _ := binOp_hasDecEq.
Definition binOp_hasChoice := [derive hasChoice for Op.bin].
HB.instance Definition _ := binOp_hasChoice.
Definition binOp_isCountable := [derive isCountable for Op.bin].
HB.instance Definition _ := binOp_isCountable.

Inductive formula : Type :=
  | Var of nat
  | Bot
  | BinOp of Op.bin & formula & formula.
Bind Scope NJ_scope with formula.

Definition formula_indDef := [indDef for formula_rect].
Canonical formula_indType := IndType formula formula_indDef.

Definition formula_hasDecEq := [derive hasDecEq for formula].
HB.instance Definition _ := formula_hasDecEq.
Definition formula_hasChoice := [derive hasChoice for formula].
HB.instance Definition _ := formula_hasChoice.
Definition formula_isCountable := [derive isCountable for formula].
HB.instance Definition _ := formula_isCountable.

Notation Or := (BinOp Op.Or).
Notation And := (BinOp Op.And).
Notation Imply := (BinOp Op.Imply).

Notation "A ∨ B" := (Or A B) (at level 85) : NJ_scope.
Notation "A ∧ B" := (And A B) (at level 80) : NJ_scope.
Notation "A ⇒ B" := (Imply A B) (right associativity, at level 99) : NJ_scope.
Notation "⊥" := Bot : NJ_scope.
Notation Neg := (fun A => (A ⇒ ⊥)).
Notation "¬ A" := (A ⇒ ⊥) (at level 75) : NJ_scope.
Notation Top := (¬ ⊥).
Notation "⊤" := Top : NJ_scope.
Notation P_ n := (Var n).
Notation "'P_ n" := (P_ n) : NJ_scope.

Fixpoint size_formula (A : formula) : nat :=
  match A with
  | Var _ => 1
  | Bot => 1
  | BinOp op A B => size_formula A + size_formula B
  end.

Lemma size_formula_gt0 (A : formula) : size_formula A > 0.
Proof.
elim: A => [//|//|op A A0 B B0]/=.
by rewrite addn_gt0 A0.
Qed.
Hint Resolve size_formula_gt0 : core.

Fixpoint subst_formula (ρ : list formula) (f : formula) :=
  match f with
  | Var n => nth 'P_(n - size ρ) ρ n
  | Bot => Bot
  | BinOp op f f' => BinOp op (subst_formula ρ f) (subst_formula ρ f')
  end.

(************)
(* Sequents *)
(************)

Record sequent := Sequent {
  hypotheses : list formula;
  thesis : formula
}.
Bind Scope NJ_scope with sequent.

Scheme sequent_rect := Induction for sequent Sort Type.
Definition sequent_indDef := [indDef for sequent_rect].
Canonical sequent_indType := IndType sequent sequent_indDef.
Definition sequent_hasDecEq := [derive hasDecEq for sequent].
HB.instance Definition _ := sequent_hasDecEq.
Definition sequent_hasChoice := [derive hasChoice for sequent].
HB.instance Definition _ := sequent_hasChoice.
Definition sequent_isCountable := [derive isCountable for sequent].
HB.instance Definition _ := sequent_isCountable.

Coercion singlef (f : formula) := [:: f].
Notation "Γ ⊢ B" := (Sequent Γ B) (at level 100) : NJ_scope.
Notation "⊢ B" := (Sequent [::] B) (at level 100) : NJ_scope.

Definition subst_sequent (ρ : list formula) (s : sequent) :=
  Sequent (map (subst_formula ρ) (hypotheses s)) (subst_formula ρ (thesis s)).

Definition map_sequent (f : formula -> formula) (s : sequent) :=
  Sequent (map f (hypotheses s)) (f (thesis s)).

Definition formulae (s : sequent) := thesis s :: hypotheses s.

(*********)
(* Rules *)
(*********)

Record rule := Rule {
  premises : list sequent;
  conclusion : sequent
}.
Bind Scope NJ_scope with rule.

Scheme rule_rect := Induction for rule Sort Type.
Definition rule_indDef := [indDef for rule_rect].
Canonical rule_indType := IndType rule rule_indDef.
Definition rule_hasDecEq := [derive hasDecEq for rule].
HB.instance Definition _ := rule_hasDecEq.
Definition rule_hasChoice := [derive hasChoice for rule].
HB.instance Definition _ := rule_hasChoice.
Definition rule_isCountable := [derive isCountable for rule].
HB.instance Definition _ := rule_isCountable.

Coercion single_sequent (f : sequent) := [:: f].
Notation "p -------------- c" := (Rule p c)
  (format "'[v   ' '//' '[' p ']' '//' -------------- '//' '[' c ']' '//' ']'",
   at level 150) : NJ_scope.
Coercion JustConcl (s : sequent) : rule := Rule [::] s.

(********************************)
(* Derivations and derivability *)
(********************************)

Inductive derivation (hyps : seq sequent) : sequent -> Type :=
| Hyp s : s ∈ hyps -> derivation s
| Ax Γ i A : tnth (in_tuple Γ) i = A -> derivation (Γ ⊢ A)
| BotE Γ A : derivation (Γ ⊢ ⊥) -> derivation (Γ ⊢ A)
| AndI Γ A B (l : derivation (Γ ⊢ A)) (r : derivation (Γ ⊢ B)) :
   derivation (Γ ⊢ A ∧ B)
| AndE1 Γ A B : derivation (Γ ⊢ A ∧ B) -> derivation (Γ ⊢ A)
| AndE2 Γ A B : derivation (Γ ⊢ A ∧ B) -> derivation (Γ ⊢ B)
| OrI1 Γ A B : derivation (Γ ⊢ A) -> derivation (Γ ⊢ A ∨ B)
| OrI2 Γ A B : derivation (Γ ⊢ B) -> derivation (Γ ⊢ A ∨ B)
| OrE Γ A B C (l : derivation (Γ ⊢ A ∨ B))
              (m : derivation (A :: Γ ⊢ C))
              (r : derivation (B :: Γ ⊢ C)) :
                derivation (Γ ⊢ C)
| ImplyI Γ A B : derivation (A :: Γ ⊢ B) -> derivation (Γ ⊢ A ⇒ B)
| ImplyE Γ A B (l : derivation (Γ ⊢ A)) (r : derivation (Γ ⊢ A ⇒ B)) :
                 derivation (Γ ⊢ B).

Arguments Ax {_ _}.

Derive Dependent Inversion derivationP
 with (forall hyps s, derivation hyps s) Sort Type.

Definition derivable (r : rule) := derivation (premises r) (conclusion r).
Notation provable x := (derivation [::] (⊢ x)).

(* casting from derivation ps c to derivable (Rule ps c) *)
Coercion derivable_of_derivation ps c (d : derivation ps c) :
   derivable (Rule ps c) := d.

Fixpoint depth_derivation hyps s (d : derivation hyps s) :=
  match d with
  | Hyp s x => 0
  | Ax Γ i A x => 1
  | BotE Γ A x => (depth_derivation x).+1
  | AndI Γ A B l r => (maxn (depth_derivation l) (depth_derivation r)).+1
  | AndE1 Γ A B x => (depth_derivation x).+1
  | AndE2 Γ A B x => (depth_derivation x).+1
  | OrI1 Γ A B x => (depth_derivation x).+1
  | OrI2 Γ A B x => (depth_derivation x).+1
  | OrE Γ A B C l m r => (maxn (maxn (depth_derivation l)
    (depth_derivation m)) (depth_derivation r)).+1
  | ImplyI Γ A B x => (depth_derivation x).+1
  | ImplyE Γ A B l r => (maxn (depth_derivation l) (depth_derivation r)).+1
  end.

Definition subst_derivation (ρ : list formula) hyps (s : sequent)  :
   derivation hyps s ->
   derivation (map (subst_sequent ρ) hyps) (subst_sequent ρ s).
Proof.
elim=> //=; do ?by constructor.
- by move=> h ?; apply/Hyp/map_f.
- move=> Γ i _ <- /=.
  apply: (Ax [ord i]); first by rewrite size_map.
  by move=> ? /=;  apply: tnth_in_tuple_map.
- by move=> Γ A B ?; apply: AndE1.
- by move=> Γ A B ?; apply: AndE2.
- by move=> Γ A B C ? + ? + ?; apply: OrE.
- by move=> Γ A B ? + ?; apply: ImplyE.
Defined.

Lemma NegI [hyps : seq sequent] [Γ : seq formula] [A : formula] :
  derivation hyps (A :: Γ ⊢ ⊥) -> derivation hyps (Γ ⊢ ¬ A).
Proof. exact: ImplyI. Qed.

Lemma NegE [hyps : seq sequent] [Γ : seq formula] [A : formula] :
    derivation hyps (Γ ⊢ ¬ A) -> derivation hyps (Γ ⊢ A) ->
  derivation hyps (Γ ⊢ ⊥).
Proof. move/[swap]; exact: ImplyE. Qed.

Lemma TopI (hyps : seq sequent) (Γ : seq formula) : derivation hyps (Γ ⊢ ⊤).
Proof. by apply: NegI; apply: (Ax [ord 0]). Qed.

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

Definition simp := (mem_head, in_cons, eqxx, orbT).

Lemma Ax_derivable Γ i : derivable (@Rule.Ax Γ i). Proof. exact: Ax. Qed.

Lemma TopI_derivable Γ : derivable (Rule.TopI Γ). Proof. exact: NJ.TopI. Qed.

Lemma BotE_derivable Γ A : derivable (Rule.BotE Γ A).
Proof. by apply: NJ.BotE; apply: Hyp; rewrite mem_head. Qed.

Lemma NegI_derivable Γ A : derivable (Rule.NegI Γ A).
Proof. by apply: NJ.NegI; apply: Hyp; rewrite simp. Qed.

Lemma NegE_derivable Γ A : derivable (Rule.NegE Γ A).
Proof. by apply: (@NJ.NegE _ _ A); apply: Hyp; rewrite ?simp. Qed.

Lemma AndI_derivable Γ A B : derivable (Rule.AndI Γ A B).
Proof. by apply/NJ.AndI; apply/Hyp; rewrite ?simp. Qed.

Lemma AndE1_derivable Γ A B : derivable (Rule.AndE1 Γ A B).
Proof. by apply/(@NJ.AndE1 _ _ A B); apply/Hyp; rewrite ?simp. Qed.

Lemma AndE2_derivable Γ A B : derivable (Rule.AndE2 Γ A B).
Proof. by apply/(@NJ.AndE2 _ _ A B); apply/Hyp; rewrite ?simp. Qed.

Lemma OrI1_derivable Γ A B : derivable (Rule.OrI1 Γ A B).
Proof. by apply/NJ.OrI1; apply/Hyp; rewrite ?simp. Qed.

Lemma OrI2_derivable Γ A B : derivable (Rule.OrI2 Γ A B).
Proof. by apply/NJ.OrI2; apply/Hyp; rewrite ?simp. Qed.

Lemma OrE_derivable Γ A B C : derivable (Rule.OrE Γ A B C).
Proof. by apply/(@NJ.OrE _ _ A B); apply/Hyp; rewrite ?simp. Qed.

Lemma ImplyI_derivable Γ A B : derivable (Rule.ImplyI Γ A B).
Proof. by apply: (@NJ.ImplyI _ _ A); apply: Hyp; rewrite ?simp. Qed.

Lemma ImplyE_derivable Γ A B : derivable (Rule.ImplyE Γ A B).
Proof. by apply: (@NJ.ImplyE _ _ A); apply: Hyp; rewrite ?simp. Qed.

(***********)
(* Helpers *)
(***********)

Ltac Hyp := by apply: Hyp => /=.
Ltac EAx := by apply: Ax => /=.
Ltac Ax i := by apply: (Ax [ord i]) => /=.
Ltac TopI := apply TopI => /=.
Ltac BotE := apply BotE => /=.
Ltac NegI := apply NegI => /=.
Ltac NegE A := apply (@NegE _ _  A) => /=.
Ltac AndI := apply AndI => /=.
Ltac AndE1 B := apply (@AndE1 _ _ _ B) => /=.
Ltac AndE2 A := apply (@AndE2 _ _ A) => /=.
Ltac OrI1 := apply OrI1 => /=.
Ltac OrI2 := apply OrI2 => /=.
Ltac OrE A B := apply (@OrE _ _ A B) => /=.
Ltac ImplyI := apply ImplyI => /=.
Ltac ImplyE A := apply (@ImplyE _ _ A) => /=.

Ltac Rev := do ?[Hyp|EAx|TopI|NegI|AndI|ImplyI].

Lemma NegAx hyps Γ k :
  derivation hyps (Γ ⊢ ¬ tnth (in_tuple Γ) k) ->
  derivation hyps (Γ ⊢ ⊥).
Proof. by intros; NegE (tnth (in_tuple Γ) k) => //; EAx. Defined.
Ltac NegAx k :=
   (apply: (@NegAx _ _ [ord k]) => /=;
     do ?by []); rewrite /tnth/=.

Lemma ApNegAx hyps Γ A k :
  tnth (in_tuple Γ) k = (¬ A) ->
  derivation hyps (Γ ⊢ A) ->
  derivation hyps (Γ ⊢ ⊥).
Proof. by move=> eqNA; apply: NegE; rewrite -eqNA; EAx. Defined.
Ltac ApNegAx k :=
   (apply: (@ApNegAx _ _ _ [ord k]) => /=;
     do ?by []); rewrite /tnth/=.

Lemma OrAx hyps Γ A B C k :
                tnth (in_tuple Γ) k = (A ∨ B) ->
                derivation hyps (A :: Γ ⊢ C) ->
                derivation hyps (B :: Γ ⊢ C) ->
                derivation hyps (Γ ⊢ C).
Proof. by move=> eqAB; apply: OrE; rewrite -eqAB; EAx. Defined.
Ltac OrAx k :=
   (apply: (@OrAx _ _ _ _ _ [ord k]) => /=;
     do ?by []); rewrite /tnth/=.

Lemma AndAx hyps Γ A B k :
                sum (tnth (in_tuple Γ) k = (A ∧ B))
                    (tnth (in_tuple Γ) k = (B ∧ A)) ->
                derivation hyps (Γ ⊢ A).
Proof.
by move=> [] eqAB; [AndE1 B|AndE2 B]; rewrite -eqAB; apply: Ax.
Defined.
Ltac AndAx k :=
   (apply: ( @AndAx _ _ _ _ [ord k]) => /=;
     do ?by [|left|right]); rewrite /tnth/=.

Lemma ImplyAx hyps Γ A B k :
                tnth (in_tuple Γ) k = (A ⇒ B) ->
                derivation hyps (Γ ⊢ A) ->
                derivation hyps (Γ ⊢ B).
Proof. move=> eqAB /ImplyE; apply; rewrite -eqAB; EAx. Defined.
Ltac ImplyAx k :=
   (apply: (@ImplyAx _ _ _ _ [ord k]) => /=;
     do ?by []); rewrite /tnth/=.

(**********)
(* Theory *)
(**********)

Lemma derivationW (hyp1 hyp2 : list sequent) s : all [in hyp2] hyp1 ->
  derivation hyp1 s -> derivation hyp2 s.
Proof.
move=> /all_memP hypS; elim=> [^~0]; do ?by constructor.
- by apply: Hyp; apply: hypS.
- exact: (Ax i0).
- by AndE1 B0.
- by AndE2 A0.
- by OrE A0 B0.
- by ImplyE A0.
Defined.

Definition derivations hyps (ls : list sequent) : Type :=
  foldr (fun f P => P * derivation hyps f)%type unit ls.

Definition admissible hyps (r : rule) :=
  derivations hyps (premises r) -> derivation hyps (conclusion r).

Definition reversible hyps (r : rule) :=
  derivation hyps (conclusion r) -> derivations hyps (premises r).

Lemma derivable_admissible hyps r (rd : derivable r) : admissible hyps r.
Proof.
move: rd => /[swap]; rewrite /derivable/=; move: (premises r) => ps ders.
elim=> //=; do ?by constructor.
- move=> s; elim: ps ders => //= p ps IHps [derps derp]; rewrite in_cons.
  by case: eqP => [->//|_]/= /IHps; apply.
- by move=> ? ? ?; apply: Ax.
- by move=> ? ? ? ?; apply: AndE1.
- by move=> ? ? ? ?; apply: AndE2.
- by move=> ? ? ? ? ? + ? + ?; apply: OrE.
- by move=> ? ? ? ? + ? +; apply: ImplyE.
Qed.

Fixpoint actual_premises_subdef ps c (d : derivation ps c) : seq sequent :=
  match d with
  | Hyp s x => [:: s]
  | Ax Γ i A x => [::]
  | BotE Γ A x => actual_premises_subdef x
  | AndI Γ A B l r => actual_premises_subdef l ++ actual_premises_subdef r
  | AndE1 Γ A B x => actual_premises_subdef x
  | AndE2 Γ A B x => actual_premises_subdef x
  | OrI1 Γ A B x => actual_premises_subdef x
  | OrI2 Γ A B x => actual_premises_subdef x
  | OrE Γ A B C l m r => actual_premises_subdef l ++
                         actual_premises_subdef m ++ actual_premises_subdef r
  | ImplyI Γ A B x => actual_premises_subdef x
  | ImplyE Γ A B l r => actual_premises_subdef l ++ actual_premises_subdef r
  end.

Lemma actual_premises_subdef_sub r (d : derivable r) :
  {subset actual_premises_subdef d <= premises r}.
Proof.
move: d; rewrite /derivable/=; elim=> //=.
- by move=> s spr x; rewrite in_cons orbF => /eqP->.
- by move=> ? ? ? ? lr ? rr x; rewrite mem_cat => /orP[/lr|/rr].
- by move=> ? ? ? ? ? lr ? mr ? rr x; rewrite !mem_cat => /or3P[/lr|/mr|/rr].
- by move=> ? ? ? ? lr ? rr x; rewrite mem_cat => /orP[/lr|/rr].
Qed.

Definition actual_premises ps c (d : derivation ps c) : seq sequent :=
  filter [in actual_premises_subdef d] ps.

Lemma actual_premisesE ps c (d : derivation ps c) :
  actual_premises d =i actual_premises_subdef d.
Proof.
move=> x; rewrite /actual_premises mem_filter andb_idr//.
exact/(@actual_premises_subdef_sub _ d).
Qed.

Lemma actual_premises_sub r (d : derivable r) :
  subseq (actual_premises d) (premises r).
Proof. exact/filter_subseq. Qed.

Lemma derivable_actual_premises r (d : derivable r) :
  derivable (Rule (actual_premises d) (conclusion r)).
Proof.
move: d; rewrite /derivable/= => d; apply/derivationW.
  by apply/all_memP => x; rewrite actual_premisesE; exact: id.
elim: d => //=; do ?by constructor.
- by move=> s ?; apply: Hyp; rewrite mem_head.
- by move=> ? ? ?; apply: Ax.
- by move=> ? ? ? ? dl ? dr;
  apply: AndI; [apply: derivationW dl|apply: derivationW dr];
  apply/all_memP => ?; rewrite mem_cat => ->; rewrite ?orbT.
- by move=> ? ? ? ?; apply: AndE1.
- by move=> ? ? ? ?; apply: AndE2.
- by move=> ? ? ? ? ? dl ? dm ? dr;
  apply: OrE; [apply: derivationW dl|apply: derivationW dm|apply: derivationW dr];
  apply/all_memP => ?; rewrite !mem_cat => ->; rewrite ?orbT.
- by move=> ? ? ? ? dl ? dr;
  apply: ImplyE; [apply: derivationW dl|apply: derivationW dr];
  apply/all_memP => ?; rewrite mem_cat => ->; rewrite ?orbT.
Qed.

Lemma cut_hypotheses hyps2 hyps1 hyps s1 s2 :
  all [in hyps] hyps1 ->
  all [in hyps] hyps2 ->
  derivation (s1 :: hyps2) s2 ->
  derivation hyps1 s1 ->
  derivation hyps s2.
Proof.
move=> h1 /all_memP h2 /[swap] ders1.
elim=> [^~0]; do ?by constructor.
- move: i0; rewrite in_cons.
  case: eqP => [->_|/= _ /h2]; last exact: Hyp.
  by apply/derivationW : ders1.
- exact: (Ax i0).
- by AndE1 B0.
- by AndE2 A0.
- by OrE A0 B0.
- by ImplyE A0.
Qed.

Lemma cut_derivable Γ A B : derivable (
                      [:: A :: Γ ⊢ B ; Γ ⊢ A]
                      --------------
                      (Γ ⊢ B)
                    ).
Proof.
ImplyE A.
  by apply: Hyp; rewrite in_cons mem_head orbT.
by Rev; apply: Hyp; rewrite mem_head.
Defined.

Lemma cut Γ A B : derivable (A :: Γ ⊢ B) ->
  derivable (Γ ⊢ A) -> derivable (Γ ⊢ B).
Proof. by move=> *; apply: (derivable_admissible (cut_derivable Γ A B)). Qed.

Lemma gen_cut  hyps1 hyps2 hyps Γ A B :
  all [in hyps] hyps1 ->
  all [in hyps] hyps2 ->
  derivation hyps1 (Γ ⊢ A) ->
  derivation hyps2 (A :: Γ ⊢ B) ->
  derivation hyps (Γ ⊢ B).
Proof.
move=> /all_memP h1 h2 a; apply/cut_hypotheses => //.
ImplyE A.
  apply/(@derivationW hyps1) => //; apply/all_memP => p /h1.
  by rewrite in_cons => ->; rewrite orbT.
by Rev; apply: Hyp; rewrite mem_head.
Qed.

Lemma weakeningr Γ Γ' B : admissible [::] (
                              (Γ ⊢ B)
                              --------------
                              (Γ ++ Γ' ⊢ B)
                            ).
Proof.
case=> /= _; set s := Γ ⊢ B; rewrite -[B]/(thesis s) -[Γ]/(hypotheses s).
elim => //=; do ?by constructor.
- move=> {s}Γ i _ <-; apply: (Ax [ord i]) => [|i_lt]/=.
    by rewrite size_cat (leq_trans (ltn_ord i))// leq_addr.
  by rewrite /tnth/= nth_cat ltn_ord/=; apply/set_nth_default.
- by move=> ? ? ? ?; apply: AndE1.
- by move=> ? ? ? ?; apply: AndE2.
- by move=> ? ? ? ? ? + ? + ?; apply: OrE.
- by move=> ? ? ? ? + ? +; apply: ImplyE.
Qed.

Lemma derivable_suffix (r : rule) (d : derivable r) :
  all (fun s => suffix (hypotheses (conclusion r)) (hypotheses s)) (actual_premises d).
Proof.
rewrite (eq_all_r (actual_premisesE _)); move: d; rewrite /derivable/=.
elim=> //=.
- by move=> ? ?; rewrite suffix_refl.
- by move=> *; rewrite all_cat; apply/andP; split.
- by move=> ? ? ? ? ? le_l ? le_m ? le_r; rewrite !all_cat;
  apply/and3P; split => //;
  [move: le_m|move: le_r];
  apply: sub_all; rewrite -cat1s => ? /catl_suffix.
- by move=> ? ? ? ?; apply: sub_all; rewrite -cat1s => ? /catl_suffix.
- by move=> *; rewrite all_cat; apply/andP; split.
Qed.

Lemma weakening Γ Γ' A : {subset Γ <= Γ'} ->
  derivation [::] (Γ ⊢ A) -> derivation [::] (Γ' ⊢ A).
Proof.
move/[swap]; set s := Γ ⊢ A.
rewrite -[A]/(thesis s) -[Γ]/(hypotheses s); move: s => {Γ}s der_s.
elim: der_s Γ'  => {s} //=; do ?by constructor.
- move=> ? ? {}A AinΓ Γ' leΓ.
  suff /tnthP/sig_eqW[/= i ->] : A ∈ in_tuple Γ' by apply: (Ax i).
  by rewrite leΓ// -AinΓ mem_tnth.
- by move=> ? ? ? IH Γ /IH; apply: BotE.
- by move=> ? ? ? ? IHA ? IHB Γ leΓ; apply: AndI; [apply: IHA|apply: IHB].
- by move=> ? ? ? ? IHAB Γ leΓ; apply: AndE1; apply: IHAB.
- by move=> ? ? ? ? IHAB Γ leΓ; apply: AndE2; apply: IHAB.
- by move=> ? ? ? ? IH Γ leΓ; apply: OrI1; apply: IH.
- by move=> ? ? ? ? IH Γ leΓ; apply: OrI2; apply: IH.
- move=> ? ? ? ? ? IHV ? IHA ? IHB Γ leΓ.
  by apply: OrE; [apply: IHV|apply: IHA|apply: IHB] => // ?;
     apply/subset_cons2.
- by move=> ? ? ? ? IH Γ leΓ; apply: ImplyI; apply/IH/subset_cons2.
- by move=> ? ? ? ? IHA ? IHB Γ leΓ; apply: ImplyE (IHB _ leΓ); apply: IHA.
Qed.

Lemma derivation_tact n (Γ : n.-tuple formula) A (σ : 'S_n) :
  derivable (Γ ⊢ A) -> derivable (tact σ Γ ⊢ A).
Proof.
suff: forall Γ A (σ : 'S__), derivable (Γ ⊢ A) ->
    derivable (tact σ (in_tuple Γ) ⊢ A).
  move=> /(_ Γ A (cast_perm (esym (size_tuple Γ)) σ))/[apply].
  by rewrite in_tuple_tuple; case: _ / esym.
move=> {}Γ {}A {}σ; rewrite /derivable/=; set s := Γ ⊢ A.
move: σ; rewrite -[A]/(thesis s) -[Γ]/(hypotheses s).
move: s => {Γ}s + der_s.
elim: der_s => {s} //=; do ?by constructor.
- move=> ? i ? eqA σ.
  apply: (Ax [ord σ^-1%g i]).
     by rewrite size_tuple.
  move=> ?; rewrite tnth_in_tuple/= -eqA; set j := cast_ord _ _.
  rewrite (val_inj (erefl : val j = val (σ^-1%g i))).
  by rewrite tnth_tact permKV.
- by move=> ? ? ? ? IHAB σ; apply: AndE1; apply: IHAB.
- by move=> ? ? ? ? IHAB σ; apply: AndE2; apply: IHAB.
- move=> ? ? ? ? ? IHV ? IHA ? IHB σ; apply: OrE; first apply: IHV.
    by rewrite -tval_tact_lift0 -in_tuple_cons; apply/IHA.
  by rewrite -tval_tact_lift0 -in_tuple_cons; apply/IHB.
- move=> ? ? ? ? IH σ; apply: ImplyI.
  by rewrite -tval_tact_lift0 -in_tuple_cons; apply/IH.
- by move=> ? ? ? ? IHA ? IHB σ; apply: ImplyE (IHB σ); apply: IHA.
Qed.

Lemma derivation_perm Γ Γ' A : perm_eq Γ' Γ ->
  derivable (Γ ⊢ A) -> derivable (Γ' ⊢ A).
Proof.
elim/(@in_tupleP formula): Γ => n Γ /tactP/sig_eqW[/= σ ->].
exact/derivation_tact.
Qed.

Fixpoint subformula A B := (A == B) ||
  match B with
  | BinOp op B C => subformula A B || subformula A C
  | _ => false
  end.

Fixpoint lift_formula (f : formula) :=
  match f with
  | Var n => 'P_n.+1
  | Bot => Bot
  | BinOp op f f' => BinOp op (lift_formula f) (lift_formula f')
  end.

Lemma subst1_lift_formula A f : subst_formula [:: A] (lift_formula f) = f.
Proof.
elim: f => /= [n||op B -> C ->]//=.
by rewrite subn1 nth_default.
Qed.

Lemma subformulaP (A B : formula) :
  reflect (exists2 F, subformula 'P_0 F & B = subst_formula [:: A] F)
          (subformula A B).
Proof.
elim: B => [n||op B IHB C IHC]/=;
    rewrite ?(orbF, orbT).
- apply/(iffP idP) => [/eqP->|]; first by exists 'P_0.
  by case; case => // -[]//= _ ->.
- apply/(iffP idP) => [/eqP->|]; first by exists 'P_0.
  by case; case => // -[]//= _ ->.
- apply/(iffP or3P) => [[/eqP->|/IHB//|/IHC//]|]; first by exists 'P_0.
  - by move=> [F F0 ->]; exists (BinOp op F (lift_formula C));
       rewrite //= ?F0//= ?subst1_lift_formula.
  - by move=> [F F0 ->]; exists (BinOp op (lift_formula B) F);
       rewrite //= ?F0 ?orbT //= ?subst1_lift_formula//.
  move=> [[]]//= => [n /[!orbF]/eqP[<-]//= <-|]; first exact: Or31.
  move=> _ F G /orP[F0|G0] [_ BE CE]; [apply: Or32|apply: Or33].
    by apply/IHB; exists F.
  by apply/IHC; exists G.
Qed.

Lemma subformula_refl : reflexive subformula.
Proof. by case=> //= *; rewrite eqxx. Qed.
Hint Resolve subformula_refl : core.

Definition subformulaxx x : subformula x x := subformula_refl x.
Hint Resolve subformulaxx : core.

Lemma subformula_neg {A} : subformula A (¬ A).
Proof. by apply/subformulaP; exists (¬ 'P_0). Qed.
Hint Resolve subformula_neg : core.

Lemma subformula_binopl {op A B} : subformula A (BinOp op A B).
Proof.
apply/subformulaP; exists (BinOp op 'P_0 (lift_formula B)) => //=.
by rewrite subst1_lift_formula.
Qed.
Hint Resolve subformula_binopl : core.

Lemma subformula_binopr {op A B} : subformula B (BinOp op A B).
Proof.
apply/subformulaP; exists (BinOp op (lift_formula A) 'P_0);
by rewrite /= ?orbT// subst1_lift_formula.
Qed.
Hint Resolve subformula_binopr : core.

Lemma subformula_trans : transitive subformula.
Proof.
move=> + + A.
elim: A => /= [n||op A IHA B IHB] [n'||/= op' A' B'] C //=;
    rewrite /= ?orbF//=; do ?by move=> /eqP->.
move=> /or3P[/eqP->//|CA'|CB'] /or3P[/eqP[_ /[-->] /[-->]]//||].
- by rewrite CA' ?orbT.
- by move=> /(IHA _ _ subformula_binopl)/(IHA _ _ CA')->; rewrite ?orbT.
- by move=> /(IHB _ _ subformula_binopl)/(IHB _ _ CA')->; rewrite ?orbT.
- by rewrite CB' ?orbT.
- by move=> /(IHA _ _ subformula_binopr)/(IHA _ _ CB')->; rewrite ?orbT.
- by move=> /(IHB _ _ subformula_binopr)/(IHB _ _ CB')->; rewrite ?orbT.
Qed.

Lemma Neg_inj : injective Neg. Proof. by move=> ? ? []. Qed.
Lemma BinOpr_inj op A : injective (BinOp op A) . Proof. by move=> ? ? []. Qed.
Lemma BinOpl_inj op A : injective ((BinOp op)^~ A) .
Proof. by move=> ? ? []. Qed.

Lemma subformula_size A B : subformula A B -> size_formula A <= size_formula B.
Proof.
move=> /subformulaP/=[+ + ->].
elim=> [n|b|op F IHF G IHG]//=; rewrite ?orbF//=.
- by move=> /eqP[<-]/=.
- by move=> /orP[{}/IHF IH|{}/IHG IH];
  rewrite (leq_trans IH)// (leq_addl,leq_addr).
Qed.

Lemma neq_BinOpl op A B : (BinOp op A B) != A.
Proof.
apply/eqP => /(congr1 size_formula)/= /eqP.
by rewrite -[X in _ == X]addn0 eqn_add2l gtn_eqF//.
Qed.

Lemma neq_BinOpr op A B : (BinOp op A B) != B.
Proof.
apply/eqP => /(congr1 size_formula)/= /eqP.
by rewrite -[X in _ == X]add0n eqn_add2r gtn_eqF//.
Qed.

Lemma neq_Neg A : (¬ A) != A. Proof. by rewrite !neq_BinOpl. Qed.

Lemma subformula_anti : antisymmetric subformula.
Proof.
move=> A _ /andP[/subformulaP/=[F F0 ->]] FA.
gen have Feq0 : A F F0 FA / F = 'P_0; last by move: FA => /Feq0-/(_ F0)->.
elim: F A F0 FA => [n||op F IHF G IHG] A; rewrite /= ?orbF //=.
- by move=> /eqP->.
- move=> /orP[F0|G0] FGA.
    have /IHF-/(_ F0) {}F0 := subformula_trans subformula_binopl FGA.
    move: FGA; rewrite F0/= => /subformula_size/=.
    by rewrite -leq_psubRL// subnn ltn_geF.
  have /IHG-/(_ G0) {}G0 := subformula_trans subformula_binopr FGA.
  move: FGA; rewrite G0/= => /subformula_size/=.
  by rewrite addnC -leq_psubRL// subnn ltn_geF.
Qed.

HB.instance Definition _ :=
  Order.Le_isPOrder.Build tt formula subformula_refl  subformula_anti subformula_trans.
Bind Scope order_scope with formula.


Lemma lefP (A B : formula) :
  reflect (exists2 F, ('P_0 <= F)%O & B = subst_formula [:: A] F)
          (A <= B)%O.
Proof. exact: subformulaP. Qed.


Lemma le_size_formula :
   {homo size_formula : A B / (A <= B)%O >-> (A <= B)%N}.
Proof. exact: subformula_size. Qed.

Lemma lef_def (A B : formula) : (A <= B)%O = (A == B) ||
  match B with
  | BinOp op B C => (A <= B)%O || (A <= C)%O
  | _ => false
  end.
Proof. by case: B. Qed.


Lemma ltf_def (A B : formula) : (A < B)%O =
  match B with
  | BinOp op B C => (A <= B)%O || (A <= C)%O
  | _ => false
  end.
Proof.
symmetry; rewrite lt_neqAle lef_def; case: eqP => //= <-.
case: A => //= op A {}B; apply/negP => /orP[]/le_size_formula//=.
  by rewrite -leq_subRL ?subnn// ltn_geF//.
by rewrite addnC -leq_subRL ?subnn// ltn_geF.
Qed.

Lemma lt_Var A i : (A < 'P_i)%O = false. Proof. by rewrite ltf_def. Qed.

Lemma lt_Bot A : (A < ⊥)%O = false. Proof. by rewrite ltf_def. Qed.

Lemma lt_BinOp op A B C : (A < BinOp op B C)%O = (A <= B)%O || (A <= C)%O.
Proof. by rewrite ltf_def. Qed.

Lemma lt_BinOpl op A B : (A < BinOp op A B)%O.
Proof. by rewrite ltf_def lexx. Qed.

Lemma lt_BinOpr op A B : (B < BinOp op A B)%O.
Proof. by rewrite ltf_def lexx orbT. Qed.

Lemma le_Var A i : (A <= 'P_i)%O = (A == 'P_i).
Proof. by rewrite lef_def orbF. Qed.

Lemma le_Bot A : (A <= ⊥)%O = (A == ⊥).
Proof. by rewrite lef_def orbF. Qed.

Lemma le_BinOp op A B C : (A <= BinOp op B C)%O = 
  [|| A == BinOp op B C, (A <= B)%O | (A <= C)%O].
Proof. by []. Qed.

Lemma le_BinOpl op A B : (A <= BinOp op A B)%O.
Proof. by rewrite ltW// lt_BinOpl. Qed.

Lemma le_BinOpr op A B : (B <= BinOp op A B)%O.
Proof. by rewrite ltW// lt_BinOpr. Qed.

Definition ltfE := (lt_BinOpl, lt_BinOpr, lt_BinOp, lt_Var, lt_Bot).
Definition lefE := (le_BinOpl, le_BinOpr, le_BinOp, le_Var, le_Bot).
Definition ltefE := (lt_BinOpl, lt_BinOpr, le_BinOpl, le_BinOpr, 
                     lt_BinOp, lt_Var, lt_Bot, le_BinOp, le_Var, le_Bot).

Lemma ltf_Neg A : (A < (¬ A))%O. Proof. by rewrite ltfE. Qed.

Lemma le_subst_formula A F : ('P_0 <= F)%O ->
  (A <= subst_formula [:: A] F)%O.
Proof. by move=> F0; apply/lefP; exists F. Qed.

Lemma size_subst_formula A F : ('P_0 <= F)%O ->
   size_formula A <= size_formula (subst_formula [:: A] F).
Proof. by move=> F0; apply/le_size_formula/le_subst_formula. Qed.

Lemma ltfP (A B : formula) :
  reflect (exists2 F, ('P_0 < F)%O & B = subst_formula [:: A] F)
          (A < B)%O.
Proof.
rewrite lt_neqAle; apply/(iffP idP) => /=.
  move=> /andP[neqAB /lefP/=[F F0 FB]]; exists F => //.
  apply: contraNT neqAB; rewrite {B}FB.
  case: F F0 => //= [[|n]|]//=.
  by move=> op F G; rewrite lefE/= ltfE negb_or => + /andP[] => /orP[]->.
move=> [F F0 FB]; apply/andP; split; last first.
  by apply/lefP; exists F => //; apply: ltW.
apply: contra_eq_neq FB => <-; case: F F0 => [[|n]||]//=.
move=> op F G; rewrite ltfE => FG0.
apply/eqP => /(congr1 size_formula)/=; apply/eqP; rewrite ltn_eqF//.
case/orP : FG0 => [F0|G0].
  by rewrite (leq_ltn_trans (size_subst_formula _ F0))// addnC (ltn_add2r _ 0).
by rewrite (leq_ltn_trans (size_subst_formula _ G0))// (ltn_add2r _ 0).
Qed.


Lemma lt_size_formula :
   {homo size_formula : A B / (A < B)%O >-> (A < B)%N}.
Proof.
move=> A B /ltfP/=[+ + ->]; case => [[|n]||]//=.
move=> op F G; rewrite ltfE => /orP [F0|G0].
  by rewrite (leq_ltn_trans (size_subst_formula _ F0))// addnC (ltn_add2r _ 0).
by rewrite (leq_ltn_trans (size_subst_formula _ G0))// (ltn_add2r _ 0).
Qed.

Definition sequent_subformula A s :=
  (A <= thesis s)%O || has (>= A)%O (hypotheses s).

Definition sequents_subformula A ss := has (sequent_subformula A) ss.

Fixpoint derivation_subformula {hyps s} (d : derivation hyps s) :=
  let subs X := sequents_subformula X (s :: hyps) in
  let ders := @derivation_subformula hyps in
  match d with
  | Hyp s x => true
  | Ax Γ i A x => true
  | BotE Γ A x => subs ⊥ && ders _ x
  | AndI Γ A B l r => ders _ l && ders _ r
  | AndE1 Γ A B x => subs (A ∧ B) && ders _ x
  | AndE2 Γ A B x => subs (A ∧ B) && ders _ x
  | OrI1 Γ A B x => ders _ x
  | OrI2 Γ A B x => ders _ x
  | OrE Γ A B C l m r => [&& subs (A ∨ B), ders _ l, ders _ m & ders _ r]
  | ImplyI Γ A B x => ders _ x
  | ImplyE Γ A B l r => [&& subs (A ⇒ B), ders _ l & ders _ r]
  end.

Axiom derivation_subformulaP : forall hyps s (d : derivation hyps s),
  {d' : derivation hyps s | derivation_subformula d'}.

Lemma consistency : provable ⊥ -> False.
Proof.
move=> /derivation_subformulaP[d].
have [n] := ubnP (depth_derivation d); elim: n d => //= n IHn.
elim/derivationP => //=.
- by move=> _ Γ [+ +] + + [/[-->]].
- by move=> _ _ _ + [/[-->] ->] => d /[!(ltnS, orbF)]/=/IHn/[apply].
- by move=> _ Γ A B x [/[-->] /[-->]]; rewrite orbF//=.
- by move=> _ Γ A B x [/[-->] /[-->]]; rewrite orbF//=.
- by move=> _ Γ A B C l m r [/[-->] /[-->]]; rewrite orbF//=.
- by move=> _ Γ A B l r [/[-->] /[-->]]; rewrite orbF//=.
Qed.

Definition is_intro hyps s (d : derivation hyps s) : bool :=
  match d with
  | AndI _ _ _ _ _ | OrI1 _ _ _ _ | OrI2 _ _ _ _ | ImplyI _ _ _ _ => true
  | _ => false
  end.

Fixpoint has_disj A :=
match A with
  | BinOp Op.Or _ _ => true
  | BinOp _ A B => has_disj A || has_disj B
  | _ => false
end.

Definition has_disj_sequent s := has has_disj (formulae s).

Lemma le_has_disj A B : (A <= B)%O -> has_disj A -> has_disj B.
Proof.
elim: B A => //= [n| |op A IHA B IHB]/= C /[!lefE]//=.
- by move=> /eqP->.
- by move=> /eqP->.
- by case: op => // /or3P[{C}/eqP->|/IHA/[apply]->|/IHB/[apply]->]//= /[!orbT].
Qed.

Lemma le_has_disj_sequent A s : has (>= A)%O (formulae s) ->
   has_disj A -> has_disj_sequent s.
Proof.
rewrite /has_disj_sequent; elim: formulae => //= {}s ss IHs.
by move=> /orP[/le_has_disj/[apply]->//|/IHs/[apply]->]/[!orbT].
Qed.

Lemma proof_is_intro Γ A :
    (derivable (Γ ⊢ ⊥) -> False) ->
    ~~ has_disj_sequent (Γ ⊢ A) ->
    ~~ has (>= A)%O Γ ->
     derivable (Γ ⊢ A) ->
  { d : derivable (Γ ⊢ A) & is_intro d /\ derivation_subformula d }.
Proof.
move=> + + /hasPn/= + /derivation_subformulaP/=[d]; move: d.
set s := (Γ ⊢ A); rewrite -[Γ]/(hypotheses s) -[A]/(thesis s).
elim => //= {Γ A s}.
- move=> Γ i A <- _ _ /(_ (tnth (in_tuple Γ) i) (mem_tnth _ _)).
  by rewrite lexx.
- by move=> Γ A B l + r; exists (AndI l r).
- move=> Γ A B x _ _ _ NAΓ; rewrite /sequent_subformula lt_geF/= ?ltfE//.
  move=> /[!orbF] /andP[/hasP/sig2W[C/= CΓ]] /(@le_trans _ _ _ A).
  by move=> /[!ltefE]// /(_ isT); move/negPn; rewrite NAΓ.
- move=> Γ A B x _ _ _ NBΓ; rewrite /sequent_subformula lt_geF/= ?ltfE//.
  move=> /[!orbF] /andP[/hasP/sig2W[C/= CΓ]] /(@le_trans _ _ _ B).
  by move=> /[!ltefE]// /(_ isT); move/negPn; rewrite NBΓ.
- move=> Γ A B C l _ m _ r _ _ ndisjC _ /[!orbF]/andP[].
  by move=> /negPn/negP[]; apply: contra ndisjC => /le_has_disj_sequent; apply.
- by move=> Γ A B x; exists (ImplyI x).
- move=> Γ A B l  _ r _ _ _  NAΓ; rewrite /sequent_subformula lt_geF/= ?ltfE//.
  move=> /[!orbF]/andP[/hasP/sig2W[C/= CΓ]] /(@le_trans _ _ _ B).
  by rewrite lefE => /(_ isT); move/negPn; rewrite NAΓ.
Qed.


Lemma or_split A B : provable (A ∨ B) -> provable A + provable B.
Proof.
move=> /derivation_subformulaP/=[d].
have [n] := ubnP (depth_derivation d).
elim: n => //= n IHn in A B d *.
elim/derivationP : d => //=.
- by move=> _ _ [+ +] ? + [/[-->]].
- by move=> _ _ ? abs [/[-->]]; exfalso; apply: consistency abs.
- move=> _ ? _ C d [/[-->] /[-->]] _ /andP[]; rewrite orbF/=.
  rewrite /sequent_subformula/= !(contra_ltnF (@le_size_formula _ _))//=;
  by have := size_formula_gt0 C; lia.
- move=> _ Γ A' _ d [/[-->] /[-->]] _ /andP[]; rewrite orbF.
  rewrite /sequent_subformula/= !(contra_ltnF (@le_size_formula _ _))//=;
  by have := size_formula_gt0 A'; lia.
- by move=> _ Γ A' B' d [/[-->] /[-->] _]; left.
- by move=> _ Γ A' B' d [/[-->] _ /[-->]]; right.
- move=> p Γ A' B' C l m r [/[-->] /[-->]]/=.
  rewrite !ltnS ?orbF ?gtn_max -!andbA.
  move=> /and3P[ln mn rn] /and5P[s' _ sl sm sr].
  have [] := IHn _ _ l ln sl; [left|right].
    (* It looks like this version of the subformula property is not enough
       indeed we have no guarantee of normal form of the derivation here *)
     admit.
  admit.
- move=> _ Γ' A' B' l r [/[-->] /[-->]] _ /andP[]; rewrite orbF/=.
  rewrite /sequent_subformula/= !(contra_ltnF (@le_size_formula _ _))//=;
  by have := size_formula_gt0 A'; lia.
Admitted.

Lemma Ax_reversible h Γ i : reversible h (@Rule.Ax Γ i). Proof. by []. Qed.

Lemma TopI_reversible h Γ : reversible h (Rule.TopI Γ). Proof. by []. Qed.

Lemma BotE_Nreversible : reversible [::] (Rule.BotE [::] ⊤) -> False.
Proof.
move=> /(_ (TopI _ _))[_] /derivation_subformulaP[d].
have [n] := ubnP (depth_derivation d); elim: n d => //= n IHn.
elim/derivationP => //=.
- by move=> _ Γ [+ +] + + [/[-->]].
- by move=> _ _ _ + [/[-->] ->] => d /[!(ltnS, orbF)]/=/IHn/[apply].
- by move=> _ Γ A B x [/[-->] /[-->]]; rewrite orbF//=.
- by move=> _ Γ A B x [/[-->] /[-->]]; rewrite orbF//=.
- by move=> _ Γ A B C l m r [/[-->] /[-->]]; rewrite orbF//=.
- by move=> _ Γ A B l r [/[-->] /[-->]]; rewrite orbF//=.
Qed.

Lemma NegI_reversible Γ A : reversible [::] (Rule.NegI Γ A).
Proof.
move=> nA; split=> //; NegE A; last by Ax 0.
by apply: weakening nA; apply/subset_cons.
Qed.

Lemma NegE_reversible h Γ A : reversible h (Rule.NegE Γ A).
Proof. by do! split; apply: BotE. Qed.

Lemma AndI_reversible h Γ A B : reversible h (Rule.AndI Γ A B).
Proof. by do !split; [AndE2 A|AndE1 B]. Qed.

Lemma AndE1_reversible : reversible [::] (Rule.AndE1 [::] ⊤ ⊥) -> False.
Proof.
by move=> /(_ (TopI _ _))[_] /AndI_reversible/= [[_]] /consistency.
Qed.

Lemma AndE2_reversible : reversible [::] (Rule.AndE2 [::] ⊥ ⊤) -> False.
Proof.
by move=> /(_ (TopI _ _))[_] /AndI_reversible/= [_] /consistency.
Qed.

Lemma OrI1_reversible : reversible [::] (Rule.OrI1 [::] ⊥ ⊤) -> False.
Proof.
move=> /(_ _)/wrap[]/=; first by OrI2; TopI.
by move=> [_ /consistency].
Qed.

Lemma OrI2_reversible : reversible [::] (Rule.OrI2 [::] ⊤ ⊥) -> False.
Proof.
move=> /(_ _)/wrap[]/=; first by OrI1; TopI.
by move=> [_ /consistency].
Qed.

Lemma OrE_reversible : reversible [::] (Rule.OrE [::] ⊥ ⊥ ⊤) -> False.
Proof.
move=> /(_ (TopI _ _))/=[[[_ _] _] prFF].
suff: provable ⊥ by apply: consistency.
by OrE ⊥ ⊥ => //; Ax 0.
Qed.

Lemma ImplyI_reversible Γ A B : reversible [::] (Rule.ImplyI Γ A B).
Proof.
move=> /= AB; split=> //; ImplyE A; first by Ax 0.
by apply: weakening AB; apply: subset_cons.
Qed.

Lemma ImplyE_reversible : reversible [::] (Rule.ImplyE [::] ⊥ ⊤) -> False.
Proof. by move=> /(_ (TopI _ _))/=[_ /consistency]. Qed.

End NJ.