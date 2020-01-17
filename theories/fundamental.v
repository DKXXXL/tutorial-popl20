From tutorial_popl20 Require Export typed compatibility interp.

(** * The fundamental theorem of logical relations

    The fundamental theorem of logical relations says that any
    syntactically typed term is also semantically typed:

    if [Γ ⊢ e : τ] then [interp Γ ρ ⊨ e : 〚τ〛 ρ]

    where [ρ] is any mapping free type variables in [Γ] and [τ] to
    semantic types.

    This theorem essentially follows from the compatibility lemmas by
    a straightforward induction on the typing derivation.  *)

Section fundamental.
  Context `{heapG Σ}.
  Implicit Types Γ : gmap string ty.
  Implicit Types τ : ty.
  Implicit Types ρ : list (sem_ty Σ).

  (* I'm not sure where I should move the following but they don't
  seem to belong here! *)
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
