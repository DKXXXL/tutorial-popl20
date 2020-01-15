From tutorial_popl20 Require Export fundamental.
From iris.heap_lang Require Import adequacy.

Lemma sem_type_safety `{heapPreG Σ} e σ es σ' e' :
  (∀ `{heapG Σ}, ∃ A, ∅ ⊨ e : A) →
  rtc erased_step ([e], σ) (es, σ') → e' ∈ es →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hty. apply (heap_adequacy Σ NotStuck e σ (λ _, True))=> // ?.
  destruct (Hty _) as [A He]. iStartProof. iDestruct (He $! ∅) as "#He".
  iSpecialize ("He" with "[]"); first by rewrite /env_sem_typed.
  rewrite subst_map_empty. iApply (wp_wand with "He"); auto.
Qed.

Lemma type_safety e σ es σ' e' τ :
  (∅ ⊢ₜ e : τ) →
  rtc erased_step ([e], σ) (es, σ') → e' ∈ es →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hty. apply (sem_type_safety (Σ:=heapΣ))=> ?.
  exists (interp τ []).
  rewrite (_ : ∅ = interp_env ∅ []); last by rewrite fmap_empty.
  by apply fundamental.
Qed.
