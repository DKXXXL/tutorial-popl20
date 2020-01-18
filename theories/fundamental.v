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
    - iApply Var_sem_typed. by apply lookup_interp_env.
    - iApply Unit_sem_typed.
    - iApply Bool_sem_typed.
    - iApply Int_sem_typed.
    - by iApply Pair_sem_typed.
    - by iApply Fst_sem_typed.
    - by iApply Snd_sem_typed.
    - by iApply InjL_sem_typed.
    - by iApply InjR_sem_typed.
    - by iApply Case_sem_typed.
    - iApply Rec_sem_typed. iSpecialize ("IH" $! ρ).
      by rewrite !interp_env_binder_insert.
    - by iApply App_sem_typed.
    - iApply TLam_sem_typed; iIntros (A). iSpecialize ("IH" $! (A :: ρ)).
      by rewrite interp_env_ty_lift /=; last lia.
    - rewrite interp_ty_subst /=; last lia.
      iApply (TApp_sem_typed with "IH").
    - iApply Pack_sem_typed. iSpecialize ("IH" $! ρ).
      by rewrite interp_ty_subst; last lia.
    - iApply (Unpack_sem_typed with "IH"); iIntros (A).
      iSpecialize ("IH1" $! (A :: ρ)).
      rewrite interp_env_binder_insert.
      rewrite interp_env_ty_lift /=; last lia.
      by rewrite interp_ty_lift /=; last lia.
    - by iApply Alloc_sem_typed.
    - by iApply Load_sem_typed.
    - by iApply Store_sem_typed.
    - by iApply FAA_sem_typed.
    - by iApply CmpXchg_sem_typed.
    - by iApply UnOp_sem_typed.
    - by iApply BinOp_sem_typed.
    - by iApply If_sem_typed.
    - by iApply Fork_sem_typed.
  Qed.
End fundamental.
