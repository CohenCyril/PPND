From HB Require Import structures.
From Coq Require Import String.
From Coq Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp Require Import finmap order.
From elpi.apps Require Import derive.std.
From deriving Require Import deriving.
From Equations Require Import Equations.
From mathcomp Require Import zify.

From ND Require Import extra NJi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import NJi.
Local Open Scope NJi_scope.
Notation Ty := formula.

Declare Scope lam_scope.
Delimit Scope lam_scope with Λ.
Local Open Scope lam_scope.

Module UnscopedDB.

Inductive Tm :=
  | Var of nat : Tm
  | Lam of Ty & Tm
  | App of Tm & Tm.

Fixpoint infer_ty (Γ : list Ty) (M : Tm) : option Ty :=
  match M with
    | Var i => onth Γ i
    | Lam A M => omap (fun B => A ⇒ B) (infer_ty (A :: Γ) M)
    | App M N =>
        match infer_ty Γ M, infer_ty Γ N with
          | Some (A ⇒ B), Some C => if A == C then Some B else None
          | _, _ => None
        end
   end.

Inductive TyOf : seq Ty -> Tm -> Ty -> Type :=
| TyVar Γ (i : nat) A : onth Γ i = Some A -> Γ ⊢ Var i : A
| TyLam Γ A B M : (A :: Γ ⊢ M : B) -> (Γ ⊢ Lam A M : A ⇒ B)
| TyApp Γ A B M N : (Γ ⊢ N : A) -> (Γ ⊢ M : A ⇒ B) -> (Γ ⊢ App M N : B)
where "Γ ⊢ M : A" := (TyOf Γ M A) : lam_scope.

Lemma infer_tyP Γ M A : infer_ty Γ M = Some A -> Γ ⊢ M : A.
Proof.
elim: M Γ A => [i | B M IHM | M IHM N IHN ]/= Γ A.
- by move=> eqΓiA; apply: TyVar.
- case tyM : (infer_ty (B :: Γ) M) => [C|//].
  move=> -[<-].
  apply: TyLam.
  by apply: IHM.
- case tyM : (infer_ty Γ M) => [[//|B C]|//].
  case tyN : (infer_ty Γ N) => [D|//].
  case: eqVneq => // eqBD [eqCA].
  apply: (@TyApp _ B).
    by apply: IHN; rewrite eqBD.
  by apply: IHM; rewrite -eqCA.
Qed.

(* Ex 1 *)
Lemma ty_inferP Γ M A : (Γ ⊢ M : A) -> infer_ty Γ M = Some A.
Admitted.

Record Tm_ (s : sequent) := mkTmOf {
  Tm_of_TmOf :> Tm;
  TmofP : infer_ty (hypotheses s) Tm_of_TmOf == Some (thesis s)
}.
Check fun Γ A => Tm_ (Γ ⊢ A).

Lemma Ty_Tm s (M : Tm_ s) : hypotheses s ⊢ M : thesis s.
Proof.
apply: infer_tyP.
apply/eqP.
exact: TmofP.
Qed.

Equations CH_rec Γ A M (Mty : (Γ ⊢ M : A)) : derivation [::] (Γ ⊢ A) :=
  CH_rec (TyVar eqiA) := @Ax [::] Γ _ A _;
  CH_rec (TyLam dM) := ImplyI (CH_rec dM);
  CH_rec (TyApp dM dN) := ImplyE (CH_rec dM) (CH_rec dN).
Next Obligation. by exists i; rewrite -onthTE eqiA. Defined.
Next Obligation. exact/tnth_onthP. Qed.

Definition CH s : Tm_ s -> derivation [::] s :=
  match s with Γ ⊢ A => fun M => CH_rec (Ty_Tm M) end.

Fixpoint CHV_rec s (d : derivation [::] s) : Tm :=
  match d with
    | Hyp _ H => match notF H with end
    | Ax Γ i A _ => Var i
    | ImplyI Γ A B d => Lam A (CHV_rec d)
    | ImplyE Γ A B l r => App (CHV_rec r) (CHV_rec l)
  end.

(* Ex 2 *)
Lemma CHV_recP s (d : derivation [::] s) :
  infer_ty (hypotheses s) (CHV_rec d) == Some (thesis s).
Admitted.

Definition CHV s (d : derivation [::] s) : Tm_ s := mkTmOf (CHV_recP d).

(* Ex 3 *)
Lemma CHK s : forall M : Tm_ s, CHV (CH M) = M.
Admitted.

(* Ex N+1 : Very difficult *)
Lemma CHVK s : forall d : derivation [::] s, CH (CHV d) = d.
Admitted.

End UnscopedDB.

Module DB.

Inductive Tm : nat -> Type :=
  | Var n of 'I_n : Tm n
  | Lam n of Ty & Tm n.+1 : Tm n
  | App n of Tm n & Tm n : Tm n.                           

End DB.

Module WS.

Inductive Tm | (X : Type) : Type :=
  | Var of X : Tm X
  | Lam of Ty & Tm (option X) : Tm X
  | App of Tm X & Tm X : Tm X.

Fixpoint Tm_map {X Y} (f : X -> Y) (M : Tm X) : Tm Y :=
  match M with
    | Var x => Var (f x)
    | Lam A M => Lam A (Tm_map (omap f) M)
    | App M N => App (Tm_map f M) (Tm_map f N)
  end.

(* Ex 4 *)
Lemma eq_Tm_map {X Y} (f g : X -> Y) : f =1 g ->
  forall M, Tm_map f M = Tm_map g M.
Admitted.

Lemma Tm_map_id {X} : Tm_map (@id X) =1 id.
Proof.
elim=> //=.
- move=> {}X A M Tm_map_M; congr Lam.
  rewrite -[RHS]Tm_map_M.
  apply/eq_Tm_map.
  by case.
- by move=> {}X M -> N ->.
Qed.

(* Ex 5 *)
Lemma Tm_map_comp {X Y Z} (f : X -> Y) (g : Y -> Z) :
    Tm_map (g \o f) =1 Tm_map g \o Tm_map f.
Proof. Admitted.

Fixpoint Tm_option {X} (M : Tm (option X)) : option (Tm X).
Admitted.
  (*  := *)
  (* match M with *)
  (* | Var x => omap (@Var _) x *)
  (* | Lam A M => omap (fun M => Lam A M) (Tm_option M) *)
  (* | App M N => _  *)
  (* end. *)

Fixpoint Tm_Tm {X} (M : Tm (Tm X)) : Tm X.
Admitted.
  (* := *)
  (* match M with *)
  (* | Var M => M *)
  (* | Lam A M => Lam A (omap Tm_Tm (Tm_option M)) *)
  (* | App M N => App (Tm_Tm M) (Tm_Tm N) *)
  (* end.     *)




End WS.
