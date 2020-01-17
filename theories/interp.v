From tutorial_popl20 Require Export sem_typed sem_type_formers types.

(** * Here we use semantic type formers to define semantics of syntactic types.

    This is done by a straightforward induction on the syntactic type.  *)

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

(** Given a syntactic typing context [Γ] (a mapping from variables
(string) to types) together with a mapping (represented as a list)
from type variables (that appear freely in [Γ]) to their corresponding
semantic types, we define a semantic typing context, i.e., a mapping
from  variables (strings) to semantic types. *)
Definition interp_env `{heapG Σ} (Γ : gmap string ty)
  (ρ : list (sem_ty Σ)) : gmap string (sem_ty Σ) := flip interp ρ <$> Γ.
Instance: Params (@interp_env) 3 := {}.

(** Below we prove several useful lemmas about [interp] and
    [interp_env] including important lemmas about the effect that
    lifting (de Bruij indices) and substitution in type level
    variables have on the interpretation of syntactic types and typing
    contexts. *)
Section interp_properties.
  Context `{heapG Σ}.
  Implicit Types Γ : gmap string ty.
  Implicit Types τ : ty.
  Implicit Types ρ : list (sem_ty Σ).
  Implicit Types i n j : nat.

  Global Instance interp_ne τ : NonExpansive ⟦ τ ⟧.
  Proof. induction τ; solve_proper. Qed.
  Global Instance interp_proper τ : Proper ((≡) ==> (≡)) ⟦ τ ⟧.
  Proof. apply ne_proper, _. Qed.

  Lemma interp_env_empty ρ : interp_env (∅ : gmap string ty) ρ = ∅.
  Proof. by rewrite /interp_env fmap_empty. Qed.
  Lemma lookup_interp_env Γ x τ ρ :
    Γ !! x = Some τ → interp_env Γ ρ !! x = Some (⟦ τ ⟧ ρ).
  Proof. intros Hx. by rewrite /interp_env lookup_fmap Hx. Qed.
  Lemma interp_env_binder_insert Γ x τ ρ :
    interp_env (binder_insert x τ Γ) ρ
    = binder_insert x (⟦ τ ⟧ ρ) (interp_env Γ ρ).
  Proof. destruct x as [|x]=> //=. by rewrite /interp_env fmap_insert. Qed.

  Lemma interp_ty_lift n τ ρ :
    n ≤ length ρ →
    ⟦ ty_lift n τ ⟧ ρ ≡ ⟦ τ ⟧ (delete n ρ).
  Proof.
    (* Use [elim:] instead of [induction] so we can properly name hyps *)
    revert n ρ. elim: τ; simpl; try (intros; done || f_equiv/=; by auto).
    - intros x n ρ ?. repeat case_decide; simplify_eq/=; try lia.
      + by rewrite lookup_delete_lt.
      + by rewrite lookup_delete_ge; last lia.
    - intros τ IH n ρ ?. f_equiv=> A /=. naive_solver auto with lia.
    - intros τ IH n ρ ?. f_equiv=> A /=. naive_solver auto with lia.
  Qed.

  Lemma interp_env_ty_lift n Γ ρ :
    n ≤ length ρ →
    interp_env (ty_lift n <$> Γ) ρ ≡ interp_env Γ (delete n ρ).
  Proof.
    intros. rewrite /interp_env -map_fmap_compose.
    apply map_fmap_equiv_ext=> x A _ /=. by rewrite interp_ty_lift.
  Qed.

  Lemma interp_ty_subst i τ τ' ρ :
    i ≤ length ρ →
    ⟦ ty_subst i τ' τ ⟧ ρ ≡ ⟦ τ ⟧ (take i ρ ++ ⟦ τ' ⟧ ρ :: drop i ρ).
  Proof.
    (* Use [elim:] instead of [induction] so we can properly name hyps *)
    revert i τ' ρ. elim: τ; simpl; try (intros; done || f_equiv/=; by auto).
    - intros x i τ' ρ ?. repeat case_decide; simplify_eq/=; try lia.
      + rewrite lookup_app_l; last (rewrite take_length; lia).
        by rewrite lookup_take; last lia.
      + by rewrite list_lookup_middle; last (rewrite take_length; lia).
      + rewrite lookup_app_r; last (rewrite take_length; lia).
        rewrite take_length lookup_cons_ne_0; last lia.
        rewrite lookup_drop. do 2 f_equiv; lia.
    - intros τ IH i τ' ρ ?. f_equiv=> A /=. rewrite IH /=; last lia.
      by rewrite interp_ty_lift; last lia.
    - intros τ IH i τ' ρ ?. f_equiv=> A /=. rewrite IH /=; last lia.
      by rewrite interp_ty_lift; last lia.
  Qed.

End interp_properties.
