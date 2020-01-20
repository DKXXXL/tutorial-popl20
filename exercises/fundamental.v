From exercises Require Export typed compatibility interp.

(** * The fundamental theorem of logical relations *)
(** The fundamental theorem of logical relations says that any syntactically
typed term is also semantically typed:

  if [Γ ⊢ e : τ] then [interp Γ ρ ⊨ e : 〚τ〛 ρ]

Here, [ρ] is any mapping free type variables in [Γ] and [τ] to semantic types.

This theorem essentially follows from the compatibility lemmas and an induction
on the typing derivation. *)

Section fundamental.
  Context `{!heapG Σ}.
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

  Lemma fundamental Γ e τ ρ
    (Hty : Γ ⊢ₜ e : τ) : (interp_env Γ ρ ⊨ e : ⟦ τ ⟧ ρ)%I
  with fundamental_val v τ ρ
    (Hty : ⊢ᵥ v : τ) : (⊨ᵥ v : ⟦ τ ⟧ ρ)%I.
  Proof.
    - destruct Hty; simpl.
      + iApply Var_sem_typed. by apply lookup_interp_env.
      + iApply Val_sem_typed; by iApply fundamental_val.
      + iApply Pair_sem_typed; by iApply fundamental.
      + iApply Fst_sem_typed; by iApply (fundamental _ _ (_ * _)%ty).
      + iApply Snd_sem_typed; by iApply (fundamental _ _ (_ * _)%ty).
      + iApply InjL_sem_typed; by iApply fundamental.
      + iApply InjR_sem_typed; by iApply fundamental.
      + iApply Case_sem_typed.
        * by iApply (fundamental _ _ (_ + _)%ty).
        * by iApply (fundamental _ _ (_ → _)%ty).
        * by iApply (fundamental _ _ (_ → _)%ty).
      + iApply Rec_sem_typed.
        change (⟦ ?τ1 ⟧ _ → ⟦ ?τ2 ⟧ _)%sem_ty with (⟦ τ1 → τ2 ⟧ ρ).
        rewrite -!interp_env_binder_insert. by iApply fundamental.
      + iApply App_sem_typed.
        * by iApply (fundamental _ _ (_ → _)%ty).
        * by iApply fundamental.
      + iApply TLam_sem_typed; iIntros (A).
        rewrite -interp_env_ty_lift_0. by iApply fundamental.
      + rewrite interp_ty_subst_0.
        iApply (TApp_sem_typed _ _ (λ A, ⟦ _ ⟧ (A :: _))).
        by iApply (fundamental _ _ (∀: _)%ty).
      + iApply (Pack_sem_typed _ _ _ (⟦ _ ⟧ ρ)).
        rewrite -interp_ty_subst_0. by iApply fundamental.
      + iApply (Unpack_sem_typed _ _ _ _ (λ A, ⟦ _ ⟧ (A :: _))).
        * by iApply (fundamental _ _ (∃: _)%ty).
        * iIntros (A).
          rewrite -(interp_ty_lift_0 _ A ρ) -(interp_env_ty_lift_0 _ A ρ).
          rewrite -interp_env_binder_insert.
          by iApply fundamental.
      + iApply Alloc_sem_typed. by iApply fundamental.
      + iApply Load_sem_typed. by iApply (fundamental _ _ (ref _)%ty).
      + iApply Store_sem_typed.
        * by iApply (fundamental _ _ (ref _)%ty).
        * by iApply fundamental.
      + iApply FAA_sem_typed.
        * by iApply (fundamental _ _ (ref TInt)%ty).
        * by iApply (fundamental _ _ TInt).
      + iApply CmpXchg_sem_typed.
        * by iApply (fundamental _ _ (ref _)%ty).
        * by iApply fundamental.
        * by iApply fundamental.
      + iApply UnOp_sem_typed. by iApply fundamental.
      + iApply BinOp_sem_typed; by iApply fundamental.
      + iApply If_sem_typed.
        * by iApply (fundamental _ _ TBool).
        * by iApply fundamental.
        * by iApply fundamental.
      + iApply Fork_sem_typed. by iApply (fundamental _ _ TUnit).
    - destruct Hty; simpl.
      + iApply UnitV_sem_typed.
      + iApply BoolV_sem_typed.
      + iApply IntV_sem_typed.
      + iApply PairV_sem_typed; by iApply fundamental_val.
      + iApply InjLV_sem_typed; by iApply fundamental_val.
      + iApply InjRV_sem_typed; by iApply fundamental_val.
      + iApply RecV_sem_typed.
        change (⟦ ?τ1 ⟧ _ → ⟦ ?τ2 ⟧ _)%sem_ty with (⟦ τ1 → τ2 ⟧ ρ).
        rewrite -(interp_env_empty ρ) -!interp_env_binder_insert.
        by iApply fundamental.
      + iApply TLamV_sem_typed; iIntros (A).
        rewrite -(interp_env_empty (A :: ρ)). by iApply fundamental.
   Qed.
End fundamental.
