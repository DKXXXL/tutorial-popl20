From tutorial_popl20 Require Export safety.

Section parametricity.
  Context `{heapG Σ}.

  (* REMOVE *) Definition exercise5_sem_ty Σ (v : val) : sem_ty Σ :=
    SemTy (λ w, ⌜w = v⌝)%I.

  Lemma exercise5 `{!heapPreG Σ} e (v : val) σ w es σ' :
    (∀ `{heapG Σ}, ∅ ⊨ e : ∀ A, A → A) →
    rtc erased_step ([e ! v]%E, σ) (of_val w :: es, σ') → w = v.
  (* REMOVE *) Proof.
    intros He.
    apply sem_gen_type_safety with (φ := λ u, u = v)=> ?.
    exists (exercise5_sem_ty Σ v). split.
    { by iIntros (?) "?". }
    iIntros (vs) "!# #Hvs".
    iPoseProof (He with "Hvs") as "He /=".
    wp_apply (wp_wand with "He").
    iIntros (u) "#Hu".
    iSpecialize ("Hu" $! (exercise5_sem_ty Σ v)).
    wp_apply (wp_wand with "Hu"). iIntros (w') "Hw'". by iApply "Hw'".
  Qed.
End parametricity.