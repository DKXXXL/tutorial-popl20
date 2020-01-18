From tutorial_popl20 Require Export language.

Inductive ty :=
  | TVar : nat → ty
  | TUnit : ty
  | TBool : ty
  | TInt : ty
  | TProd : ty → ty → ty
  | TSum : ty → ty → ty
  | TArr : ty → ty → ty
  | TForall : ty → ty
  | TExist : ty → ty
  | TRef : ty → ty.

Delimit Scope ty_scope with ty.
Bind Scope ty_scope with ty.
Notation "()" := TUnit : ty_scope.
Infix "*" := TProd : ty_scope.
Infix "+" := TSum : ty_scope.
Infix "→" := TArr : ty_scope.
Notation "∀: τ" := (TForall τ) (at level 100, τ at level 200) : ty_scope.
Notation "∃: τ" := (TExist τ) (at level 100, τ at level 200) : ty_scope.
Notation "'ref' τ" := (TRef τ) (at level 10, τ at next level, right associativity): ty_scope.

(** De Bruijn substitution *)
Fixpoint ty_lift (n : nat) (τ : ty) : ty :=
  match τ with
  | TVar y => TVar (if decide (y < n) then y else S y)%nat
  | TUnit => TUnit
  | TBool => TBool
  | TInt => TInt
  | TProd τ1 τ2 => TProd (ty_lift n τ1) (ty_lift n τ2)
  | TSum τ1 τ2 => TSum (ty_lift n τ1) (ty_lift n τ2)
  | TArr τ1 τ2 => TArr (ty_lift n τ1) (ty_lift n τ2)
  | TForall τ => TForall (ty_lift (S n) τ)
  | TExist τ => TExist (ty_lift (S n) τ)
  | TRef τ => TRef (ty_lift n τ)
  end.

Fixpoint ty_subst (x : nat) (σ : ty) (τ : ty) : ty :=
  match τ with
  | TVar y => if decide (y < x) then TVar y
              else if decide (y = x) then σ else TVar (pred y)
  | TUnit => TUnit
  | TBool => TBool
  | TInt => TInt
  | TProd τ1 τ2 => TProd (ty_subst x σ τ1) (ty_subst x σ τ2)
  | TSum τ1 τ2 => TSum (ty_subst x σ τ1) (ty_subst x σ τ2)
  | TArr τ1 τ2 => TArr (ty_subst x σ τ1) (ty_subst x σ τ2)
  | TForall τ => TForall (ty_subst (S x) (ty_lift 0 σ) τ)
  | TExist τ => TExist (ty_subst (S x) (ty_lift 0 σ) τ)
  | TRef τ => TRef (ty_subst x σ τ)
  end.
