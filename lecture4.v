From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From deriving Require Import deriving.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import extra NJi.
Import NJi.

Local Open Scope NJi_scope.

Notation Ty := formula.

Module UnScopedDb.

Inductive Tm := Var of nat | Lam of Ty & Tm | App of Tm & Tm.

Definition Id (A : Ty) := Lam A (Var 1).

Definition Tm_indDef := [indDef for Tm_rect].
Canonical Tm_indType := IndType Tm Tm_indDef.

Definition Tm_hasDecEq := [derive hasDecEq for Tm].
#[export] HB.instance Definition _ := Tm_hasDecEq.
Definition Tm_hasChoice := [derive hasChoice for Tm].
#[export] HB.instance Definition _ := Tm_hasChoice.
Definition Tm_isCountable := [derive isCountable for Tm].
#[export] HB.instance Definition _ := Tm_isCountable.

Inductive TyOf : seq Ty -> Tm -> Ty -> Type :=
| TyVar Γ i A : tnth (in_tuple Γ) i = A -> Γ ⊢ Var i : A
| TyLam Γ A B M : ((A :: Γ) ⊢ M : B) -> Γ ⊢ Lam A M : (A ⇒ B)
| TyApp Γ A B M N : (Γ ⊢ M : (A ⇒ B)) -> (Γ ⊢ N : A) -> Γ ⊢ App M N : B
where "Γ ⊢ M : A" := (TyOf Γ M A).

Fixpoint CH_rec Γ A M (Mty : Γ ⊢ M : A) : derivation [::] (Γ ⊢ A) :=
match Mty with
| TyVar Γ i A eqA => Ax _ _ eqA
| TyLam Γ A B M Mty => ImplyI (CH_rec Mty)
| TyApp Γ A B M N Mty Nty => ImplyE (CH_rec Nty) (CH_rec Mty)
end.

Definition CH Γ A (M : {M & Γ ⊢ M : A}) : derivation [::] (Γ ⊢ A) :=
  CH_rec (projT2 M).

Fixpoint CHV s (d : derivation [::] s) : {M & hypotheses s ⊢ M : thesis s} :=
match d with
| Hyp _ H => match notF H with end
| Ax Γ i A eqA => existT _ _ (TyVar eqA)
| ImplyI Γ A B d => existT _ _ (TyLam (projT2 (CHV d)))
| ImplyE Γ A B l r => existT _ _ (TyApp (projT2 (CHV r)) (projT2 (CHV l)))
end.

Lemma CHK Γ A : cancel (@CH Γ A) (@CHV (Γ ⊢ A)).
Proof.
rewrite /cancel /CH.
case => /= M.
elim => //=.
- by move=> {}Γ {}A B {}M Mty IHM; rewrite IHM/=.
- by move=> {}Γ {}A B {}M N Mty IHM Nth IHN; rewrite IHM/= IHN.
Qed.

Lemma CHVK Γ A : cancel (@CHV (Γ ⊢ A)) (@CH Γ A).
Proof.
Admitted.

Definition subst (M : Tm) (n : nat) (N : Tm) : Tm. Admitted.

Inductive Ctx :=
  Hole | CLam of Ty & Ctx | CAppl of Ctx & Tm | CAppr of Tm & Ctx.

Fixpoint substCtx (C : Ctx) N := match C with
| Hole => N
| CLam A C => Lam A (substCtx C N)
| CAppl C M => App (substCtx C N) M
| CAppr M C => App M (substCtx C N)
end.

Definition beta M N : bool := match M with
  | App (Lam A M1) M2 => N == subst M1 0 M2
  | _ => false
end.

Definition Ctx_closure R M N :=
  exists C M' N', [/\ M = substCtx C M', N = substCtx C N' & R M' N'].

Inductive beta_red : Tm -> Tm -> Prop :=
| BetaAx A M N : beta_red (App (Lam A M) N) (subst M 0 N)
| BetaLam A M N : beta_red M N -> beta_red (Lam A M) (Lam A N) 
| BetaAppl M M' N : beta_red M M' -> beta_red (App M N) (App M' N) 
| BetaAppr M N N' : beta_red N N' -> beta_red (App M N) (App M N').

Lemma beta_redP M N : Ctx_closure beta M N <-> beta_red M N.
Proof.
Admitted.

Definition maxFV : Tm -> nat. Admitted.

End UnScopedDb.

Module ScopedDb.

Inductive Tm | n : Type :=
| Var (i : 'I_n) : Tm n
| Lam (A : Ty) (M : Tm n.+1) : Tm n
| App (M N : Tm n) : Tm n.

Definition toUnScoped n : Tm n -> {M : UnScopedDb.Tm & UnScopedDb.maxFV M < n}.
Admitted.

Definition toScoped n : {M : UnScopedDb.Tm & UnScopedDb.maxFV M < n} -> Tm n.
Admitted.

End ScopedDb.

Module WellScoped.

Inductive Tm | (X : Type) : Type :=
| Var : X -> Tm X
| Lam : Ty -> Tm (unit + X) -> Tm X
| App : Tm X -> Tm X -> Tm X.

Definition toScopedDb n : ScopedDb.Tm n -> Tm 'I_n. Admitted.

Definition rmap {A X Y} (f : X -> Y) : A + X -> A + Y :=
  fun u : A + X => match u with inl a => inl a | inr x => inr (f x) end.

Fixpoint Tmap {X Y} (f : X -> Y) (M : Tm X) : Tm Y :=
match M with
| Var x => Var (f x)
| Lam A M => Lam A (Tmap (rmap f) M)
| App M N => App (Tmap f M) (Tmap f N)
end.

Lemma rmap_id {A X} : @rmap A X X id =1 id. Proof. by case. Qed.

Lemma rmapP {A X Y} (f g : X -> Y) : f =1 g -> @rmap A X Y f =1 rmap g.
Proof. by move=> eqfg []//= ?; rewrite eqfg. Qed.

Lemma TmapP {X Y} (f g : X -> Y) : f =1 g -> Tmap f =1 Tmap g.
Proof.
move=> eqfg.
move=> M.
elim: M f g eqfg => //=.
- by move=> {}X x f g ->.
- move=> {}X A M IHM f g eqfg.
Abort.
  
Lemma Tmap_id {X} (M : Tm X) : Tmap id M = M.
Proof. Abort.

End WellScoped.

Module Named.

Inductive Tm (X : Type) : Type :=
| Var : X -> Tm
| Lam : X -> Ty -> Tm -> Tm
| App : Tm -> Tm -> Tm.

End Named.
