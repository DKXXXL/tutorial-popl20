From tutorial_popl20 Require Export typing compatibility interp.

Definition interp_env `{heapG Σ} (Γ : gmap string ty)
  (ρ : list (sem_ty Σ)) : gmap string (sem_ty Σ) := flip interp ρ <$> Γ.
Instance: Params (@interp_env) 3 := {}.

Section fundamental.
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

  Instance ty_unboxed_sound τ ρ : ty_unboxed τ → SemTyUnboxed (⟦ τ ⟧ ρ).
  Proof. destruct 1; simpl; apply _. Qed.
  Instance ty_un_op_sound op τ σ ρ :
    ty_un_op op τ σ → SemTyUnOp op (⟦ τ ⟧ ρ) (⟦ σ ⟧ ρ).
  Proof. destruct 1; simpl; apply _. Qed.
  Instance ty_bin_op_sound op τ1 τ2 σ ρ :
    ty_bin_op op τ1 τ2 σ → SemTyBinOp op (⟦ τ1 ⟧ ρ) (⟦ τ2 ⟧ ρ) (⟦ σ ⟧ ρ).
  Proof. destruct 1; simpl; apply _. Qed.

  Theorem fundamental Γ e τ ρ :
    (Γ ⊢ₜ e : τ) →
    interp_env Γ ρ ⊨ e : ⟦ τ ⟧ ρ.
  Proof.
    intros Htyped. iInduction Htyped as [] "IH" forall (ρ); simpl in *.
    - iApply sem_typed_var. by apply lookup_interp_env.
    - iApply sem_typed_unit.
    - iApply sem_typed_bool.
    - iApply sem_typed_int.
    - by iApply sem_typed_pair.
    - by iApply sem_typed_fst.
    - by iApply sem_typed_snd.
    - by iApply sem_typed_injl.
    - by iApply sem_typed_injr.
    - by iApply sem_typed_case.
    - iApply sem_typed_rec. iSpecialize ("IH" $! ρ).
      by rewrite !interp_env_binder_insert.
    - by iApply sem_typed_app.
    - iApply sem_typed_tlam; iIntros (A). iSpecialize ("IH" $! (A :: ρ)).
      by rewrite interp_env_ty_lift /=; last lia.
    - rewrite interp_ty_subst /=; last lia.
      iApply (sem_typed_tapp with "IH").
    - iApply sem_typed_pack. iSpecialize ("IH" $! ρ).
      by rewrite interp_ty_subst; last lia.
    - iApply (sem_typed_unpack with "IH"); iIntros (A).
      iSpecialize ("IH1" $! (A :: ρ)).
      rewrite interp_env_binder_insert.
      rewrite interp_env_ty_lift /=; last lia.
      by rewrite interp_ty_lift /=; last lia.
    - by iApply sem_typed_alloc.
    - by iApply sem_typed_load.
    - by iApply sem_typed_store.
    - by iApply sem_typed_faa.
    - by iApply sem_typed_cmpxchg.
    - by iApply sem_typed_un_op.
    - by iApply sem_typed_bin_op.
    - by iApply sem_typed_if.
    - by iApply sem_typed_fork.
  Qed.
End fundamental.
