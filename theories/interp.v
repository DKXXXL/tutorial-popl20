From tutorial_popl20 Require Export sem_type_formers types.

Reserved Notation "⟦ τ ⟧".
Fixpoint interp `{heapG Σ} (τ : ty) (ρ : list (sem_ty Σ)) : sem_ty Σ :=
  match τ return _ with
  | TVar x => default () (ρ !! x) (* dummy in case [x ∉ ρ] *)
  | TUnit => ()
  | TBool => sem_ty_bool
  | TInt => sem_ty_int
  | TProd τ1 τ2 => ⟦ τ1 ⟧ ρ * ⟦ τ2 ⟧ ρ
  | TSum τ1 τ2 => ⟦ τ1 ⟧ ρ + ⟦ τ2 ⟧ ρ
  | TArr τ1 τ2 => ⟦ τ1 ⟧ ρ → ⟦ τ2 ⟧ ρ
  | TForall τ => ∀ X, ⟦ τ ⟧ (X :: ρ)
  | TExist τ => ∃ X, ⟦ τ ⟧ (X :: ρ)
  | TRef τ => ref (⟦ τ ⟧ ρ)
  end%sem_ty
where "⟦ τ ⟧" := (interp τ).

Instance: Params (@interp) 2 := {}.
