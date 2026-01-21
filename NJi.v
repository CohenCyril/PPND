From HB Require Import structures.
From Coq Require Import String.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From elpi.apps Require Import derive.std.
From deriving Require Import deriving.
From mathcomp Require Import zify lra ring.

From ND Require Import extra.

Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope NJi_scope.
Delimit Scope NJi_scope with NJi.
Local Open Scope NJi_scope.

Module NJi.

(************)
(* Formulae *)
(************)

Inductive formula : Type :=
  | Var of nat
  | Imply of formula & formula.
Bind Scope NJi_scope with formula.

Definition formula_indDef := [indDef for formula_rect].
Canonical formula_indType := IndType formula formula_indDef.

Definition formula_hasDecEq := [derive hasDecEq for formula].
HB.instance Definition _ := formula_hasDecEq.
Definition formula_hasChoice := [derive hasChoice for formula].
HB.instance Definition _ := formula_hasChoice.
Definition formula_isCountable := [derive isCountable for formula].
HB.instance Definition _ := formula_isCountable.

Notation "A ⇒ B" := (Imply A B) (right associativity, at level 99) : NJi_scope.
Notation P_ n := (Var n).
Notation "'P_ n" := (P_ n) : NJi_scope.

Fixpoint size_formula (A : formula) : nat :=
  match A with
  | Var _ => 1
  | A ⇒ B => size_formula A + size_formula B
  end.

Lemma size_formula_gt0 (A : formula) : size_formula A > 0.
Proof. by elim: A => [//|A A0 B B0]/=; rewrite addn_gt0 A0. Qed.
Hint Resolve size_formula_gt0 : core.

Fixpoint subst_formula (ρ : list formula) (f : formula) :=
  match f with
  | Var n => nth 'P_(n - size ρ) ρ n
  | f ⇒ f' => (subst_formula ρ f) ⇒ (subst_formula ρ f')
  end.

(************)
(* Sequents *)
(************)

Record sequent := Sequent {
  hypotheses : list formula;
  thesis : formula
}.
Bind Scope NJi_scope with sequent.

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
Notation "Γ ⊢ B" := (Sequent Γ B) (at level 100) : NJi_scope.
Notation "⊢ B" := (Sequent [::] B) (at level 100) : NJi_scope.

Definition map_sequent (f : formula -> formula) (s : sequent) :=
  Sequent (map f (hypotheses s)) (f (thesis s)).

Definition subst_sequent (ρ : list formula) (s : sequent) :=
  map_sequent (subst_formula ρ) s.

(*********)
(* Rules *)
(*********)

Record rule := Rule {
  premises : list sequent;
  conclusion : sequent
}.
Bind Scope NJi_scope with rule.

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
   at level 150) : NJi_scope.
Coercion JustConcl (s : sequent) : rule := Rule [::] s.

(********************************)
(* Derivations and derivability *)
(********************************)

Inductive derivation (hyps : seq sequent) : sequent -> Type :=
| Hyp s : s ∈ hyps -> derivation s
| Ax Γ i A : tnth (in_tuple Γ) i = A -> derivation (Γ ⊢ A)
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
- by move=> Γ A B ? + ?; apply: ImplyE.
Defined.


Module Rule.

Definition Ax Γ i : rule := Γ ⊢ tnth (in_tuple Γ) i.
Definition ImplyI Γ A B := Rule (A :: Γ ⊢ B) (Γ ⊢ A ⇒ B).
Definition ImplyE Γ A B := Rule [:: Γ ⊢ A; Γ ⊢ A ⇒ B] (Γ ⊢ B).

End Rule.

Definition simp := (mem_head, in_cons, eqxx, orbT).

Lemma Ax_derivable Γ i : derivable (@Rule.Ax Γ i). Proof. exact: Ax. Qed.

Lemma ImplyI_derivable Γ A B : derivable (Rule.ImplyI Γ A B).
Proof. by apply: (@NJi.ImplyI _ _ A); apply: Hyp; rewrite ?simp. Qed.

Lemma ImplyE_derivable Γ A B : derivable (Rule.ImplyE Γ A B).
Proof. by apply: (@NJi.ImplyE _ _ A); apply: Hyp; rewrite ?simp. Qed.

(***********)
(* Helpers *)
(***********)

Ltac Hyp := by apply: Hyp => /=.
Ltac EAx := by apply: Ax => /=.
Ltac Ax i := by apply: (Ax [ord i]) => /=.
Ltac ImplyI := apply ImplyI => /=.
Ltac ImplyE A := apply (@ImplyE _ _ A) => /=.

Ltac Rev := do ?[Hyp|EAx|ImplyI].

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
move=> /allP hypS; elim=> [^~0]; do ?by constructor.
- by apply: Hyp; apply: hypS.
- exact: (Ax i0).
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
- by move=> ? ? ? ? + ? +; apply: ImplyE.
Qed.

Fixpoint actual_premises_subdef ps c (d : derivation ps c) : seq sequent :=
  match d with
  | Hyp s x => [:: s]
  | Ax Γ i A x => [::]
  | ImplyI Γ A B x => actual_premises_subdef x
  | ImplyE Γ A B l r => actual_premises_subdef l ++ actual_premises_subdef r
  end.

Lemma actual_premises_subdef_sub r (d : derivable r) :
  {subset actual_premises_subdef d <= premises r}.
Proof.
move: d; rewrite /derivable/=; elim=> //=.
- by move=> s spr x; rewrite in_cons orbF => /eqP->.
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
  by apply/allP => x; rewrite actual_premisesE; exact: id.
elim: d => //=; do ?by constructor.
- by move=> s ?; apply: Hyp; rewrite mem_head.
- by move=> ? ? ?; apply: Ax.
- by move=> ? ? ? ? dl ? dr;
  apply: ImplyE; [apply: derivationW dl|apply: derivationW dr];
  apply/allP => ?; rewrite mem_cat => ->; rewrite ?orbT.
Qed.

Lemma cut_hypotheses hyps2 hyps1 hyps s1 s2 :
  all [in hyps] hyps1 ->
  all [in hyps] hyps2 ->
  derivation (s1 :: hyps2) s2 ->
  derivation hyps1 s1 ->
  derivation hyps s2.
Proof.
move=> h1 /allP h2 /[swap] ders1.
elim=> [^~0]; do ?by constructor.
- move: i0; rewrite in_cons.
  case: eqP => [->_|/= _ /h2]; last exact: Hyp.
  by apply/derivationW : ders1.
- exact: (Ax i0).
- by ImplyE A0.
Qed.

Lemma cut_derivable Γ A B : derivable (
                      [:: A :: Γ ⊢ B & Γ ⊢ A]
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
move=> /allP h1 h2 a; apply/cut_hypotheses => //.
ImplyE A.
  apply/(@derivationW hyps1) => //; apply/allP => p /h1.
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
- by move=> ? ? ? ? + ? +; apply: ImplyE.
Qed.

Lemma derivable_suffix (r : rule) (d : derivable r) :
  all (fun s => suffix (hypotheses (conclusion r)) (hypotheses s)) (actual_premises d).
Proof.
rewrite (eq_all_r (actual_premisesE _)); move: d; rewrite /derivable/=.
elim=> //=.
- by move=> ? ?; rewrite suffix_refl.
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
  | B ⇒ C => subformula A B || subformula A C
  | _ => false
  end.

Fixpoint lift_formula (f : formula) :=
  match f with
  | Var n => 'P_n.+1
  | f ⇒ f' => (lift_formula f) ⇒ (lift_formula f')
  end.

Lemma subst1_lift_formula A f : subst_formula [:: A] (lift_formula f) = f.
Proof. by elim: f => /= [n|B -> C ->]//=; rewrite subn1 nth_default. Qed.

Lemma subformulaP (A B : formula) :
  reflect (exists2 F, subformula 'P_0 F & B = subst_formula [:: A] F)
          (subformula A B).
Proof.
elim: B => [n|B IHB C IHC]/=;
    rewrite ?(orbF, orbT).
- apply/(iffP idP) => [/eqP->|]; first by exists 'P_0.
  by case; case => // -[]//= _ ->.
- apply/(iffP or3P) => [[/eqP->|/IHB//|/IHC//]|]; first by exists 'P_0.
  - by move=> [F F0 ->]; exists (F ⇒ (lift_formula C));
       rewrite //= ?F0//= ?subst1_lift_formula.
  - by move=> [F F0 ->]; exists ((lift_formula B) ⇒ F);
       rewrite //= ?F0 ?orbT //= ?subst1_lift_formula//.
  move=> [[]]//= => [n /[!orbF]/eqP[<-]//= <-|]; first exact: Or31.
  move=> F G /orP[F0|G0] [BE CE]; [apply: Or32|apply: Or33].
    by apply/IHB; exists F.
  by apply/IHC; exists G.
Qed.

Lemma subformula_refl : reflexive subformula.
Proof. by case=> /= *; rewrite eqxx. Qed.
Hint Resolve subformula_refl : core.

Definition subformulaxx x : subformula x x := subformula_refl x.
Hint Resolve subformulaxx : core.

Lemma subformula_implyl {A B} : subformula A (A ⇒ B).
Proof.
apply/subformulaP; exists ('P_0 ⇒ (lift_formula B)) => //=.
by rewrite subst1_lift_formula.
Qed.
Hint Resolve subformula_implyl : core.

Lemma subformula_implyr {A B} : subformula B (A ⇒ B).
Proof.
apply/subformulaP; exists ((lift_formula A) ⇒ 'P_0);
by rewrite /= ?orbT// subst1_lift_formula.
Qed.
Hint Resolve subformula_implyr : core.

Lemma subformula_trans : transitive subformula.
Proof.
move=> + + A.
elim: A => /= [n|A IHA B IHB] [n'|/= A' B'] C //=;
    rewrite /= ?orbF//=; do ?by move=> /eqP->.
move=> /or3P[/eqP->//|CA'|CB'] /or3P[/eqP[/[-->] /[-->]]//||].
- by move=> /(IHA _ _ subformula_implyl)/(IHA _ _ CA')->; rewrite ?orbT.
- by move=> /(IHB _ _ subformula_implyl)/(IHB _ _ CA')->; rewrite ?orbT.
- by move=> /(IHA _ _ subformula_implyr)/(IHA _ _ CB')->; rewrite ?orbT.
- by move=> /(IHB _ _ subformula_implyr)/(IHB _ _ CB')->; rewrite ?orbT.
Qed.

Lemma Implyr_inj A : injective (Imply A) . Proof. by move=> ? ? []. Qed.
Lemma Implyl_inj A : injective ((Imply)^~ A) .
Proof. by move=> ? ? []. Qed.

Lemma subformula_size A B : subformula A B -> size_formula A <= size_formula B.
Proof.
move=> /subformulaP/=[+ + ->].
elim=> [n|F IHF G IHG]//=; rewrite ?orbF//=.
- by move=> /eqP[<-]/=.
- by move=> /orP[{}/IHF IH|{}/IHG IH];
  rewrite (leq_trans IH)// (leq_addl,leq_addr).
Qed.

Lemma neq_Implyl A B : (A ⇒ B) != A.
Proof.
apply/eqP => /(congr1 size_formula)/= /eqP.
by rewrite -[X in _ == X]addn0 eqn_add2l gtn_eqF//.
Qed.

Lemma neq_Implyr A B : (A ⇒ B) != B.
Proof.
apply/eqP => /(congr1 size_formula)/= /eqP.
by rewrite -[X in _ == X]add0n eqn_add2r gtn_eqF//.
Qed.

Lemma subformula_anti : antisymmetric subformula.
Proof.
move=> A _ /andP[/subformulaP/=[F F0 ->]] FA.
gen have Feq0 : A F F0 FA / F = 'P_0; last by move: FA => /Feq0-/(_ F0)->.
elim: F A F0 FA => [n|F IHF G IHG] A; rewrite /= ?orbF //=.
- by move=> /eqP->.
- move=> /orP[F0|G0] FGA.
    have /IHF-/(_ F0) {}F0 := subformula_trans subformula_implyl FGA.
    move: FGA; rewrite F0/= => /subformula_size/=.
    by rewrite -leq_psubRL// subnn ltn_geF.
  have /IHG-/(_ G0) {}G0 := subformula_trans subformula_implyr FGA.
  move: FGA; rewrite G0/= => /subformula_size/=.
  by rewrite addnC -leq_psubRL// subnn ltn_geF.
Qed.

Fact formula_display : preorder.Order.disp_t. Proof. by []. Qed.
HB.instance Definition _ :=
  Order.Le_isPOrder.Build formula_display formula
    subformula_refl  subformula_anti subformula_trans.
Bind Scope order_scope with formula.


Lemma lefP (A B : formula) :
  reflect (exists2 F, ('P_0 <= F)%O & B = subst_formula [:: A] F)
          (A <= B)%O.
Proof. exact: subformulaP. Qed.


Lemma le_size_formula :
   {homo size_formula : A B / (A <= B)%O >-> (A <= B)%N}.
Proof. exact: subformula_size. Qed.

Lemma lefE (A B : formula) : (A <= B)%O = (A == B) ||
  match B with
  | Imply B C => (A <= B)%O || (A <= C)%O
  | _ => false
  end.
Proof. by case: B. Qed.

Lemma ltfE (A B : formula) : (A < B)%O =
  match B with
  | Imply B C => (A <= B)%O || (A <= C)%O
  | _ => false
  end.
Proof.
symmetry; rewrite lt_neqAle lefE; case: eqP => //= <-.
case: A => //= A {}B; apply/negP => /orP[]/le_size_formula//=.
  by rewrite -leq_subRL ?subnn// ltn_geF//.
by rewrite addnC -leq_subRL ?subnn// ltn_geF.
Qed.

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
  by move=> F G; rewrite lefE/= ltfE negb_or => + /andP[] => /orP[]->.
move=> [F F0 FB]; apply/andP; split; last first.
  by apply/lefP; exists F => //; apply: ltW.
apply: contra_eq_neq FB => <-; case: F F0 => [[|n]|]//=.
move=> F G; rewrite ltfE => FG0.
apply/eqP => /(congr1 size_formula)/=; apply/eqP; rewrite ltn_eqF//.
case/orP : FG0 => [F0|G0].
  by rewrite (leq_ltn_trans (size_subst_formula _ F0))// addnC (ltn_add2r _ 0).
by rewrite (leq_ltn_trans (size_subst_formula _ G0))// (ltn_add2r _ 0).
Qed.

Lemma lt_Implyl A B : (A < (A ⇒ B))%O.
Proof.
apply/ltfP; exists (Imply 'P_0 (lift_formula B)); rewrite ?ltfE//=.
by rewrite subst1_lift_formula.
Qed.

Lemma lt_Implyr A B : (B < (A ⇒ B))%O.
Proof.
apply/ltfP; exists (Imply (lift_formula A) 'P_0);
by rewrite ?ltfE ?lexx ?orbT//= subst1_lift_formula.
Qed.

Lemma lt_size_formula :
   {homo size_formula : A B / (A < B)%O >-> (A < B)%N}.
Proof.
move=> A B /ltfP/=[+ + ->]; case => [[|n]|]//=.
move=> F G; rewrite ltfE => /orP [F0|G0].
  by rewrite (leq_ltn_trans (size_subst_formula _ F0))// addnC (ltn_add2r _ 0).
by rewrite (leq_ltn_trans (size_subst_formula _ G0))// (ltn_add2r _ 0).
Qed.

Definition sequent_subformula A s :=
  (A <= thesis s)%O || has (>=%O A) (hypotheses s).

Definition sequents_subformula A ss := has (sequent_subformula A) ss.

Fixpoint derivation_subformula {hyps s} (d : derivation hyps s) :=
  let subs X := sequents_subformula X (s :: hyps) in
  let ders := @derivation_subformula hyps in
  match d with
  | Hyp s x => true
  | Ax Γ i A x => true
  | ImplyI Γ A B x => ders _ x
  | ImplyE Γ A B l r => [&& subs (A ⇒ B), ders _ l & ders _ r]
  end.

Axiom derivation_subformulaP : forall hyps s (d : derivation hyps s),
  {d' : derivation hyps s | derivation_subformula d'}.

Lemma Ax_reversible h Γ i : reversible h (@Rule.Ax Γ i). Proof. by []. Qed.

Lemma ImplyI_reversible Γ A B : reversible [::] (Rule.ImplyI Γ A B).
Proof.
move=> /= AB; split=> //; ImplyE A; first by Ax 0.
by apply: weakening AB; apply: subset_cons.
Qed.


End NJi.
