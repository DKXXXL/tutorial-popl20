From tutorial_popl20 Require Export fundamental.
From iris.heap_lang Require Export adequacy.

Lemma sem_type_safety `{heapPreG Σ} e σ φ :
  (∀ `{heapG Σ}, ∃ A : sem_ty Σ, (∀ x, A x -∗ ⌜φ x⌝) ∧ (∅ ⊨ e : A)) →
  adequate NotStuck e σ (λ v σ, φ v).
Proof.
  intros Hty. apply (heap_adequacy Σ NotStuck e σ)=> // ?.
  specialize (Hty _) as (A & HA & Hty).
  iStartProof. iDestruct (Hty $! ∅) as "#He".
  iSpecialize ("He" with "[]"); first by rewrite /env_sem_typed.
  rewrite subst_map_empty. iApply (wp_wand with "He"); auto.
  by iIntros; iApply HA.
Qed.

Lemma sem_type_safety' `{heapPreG Σ} e σ es σ' e' :
  (∀ `{heapG Σ}, ∃ A, ∅ ⊨ e : A) →
  rtc erased_step ([e], σ) (es, σ') → e' ∈ es →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hty.
  apply sem_type_safety with (φ := λ _, True); last done.
  intros ?; specialize (Hty _) as [A Hty].
  eauto.
Qed.

Lemma type_safety e σ es σ' e' τ :
  (∅ ⊢ₜ e : τ) →
  rtc erased_step ([e], σ) (es, σ') → e' ∈ es →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hty. apply (sem_type_safety' (Σ:=heapΣ))=> ?.
  exists (⟦ τ ⟧ []). rewrite -(interp_env_empty []).
  by apply fundamental.
Qed.
