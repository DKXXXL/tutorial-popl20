From tutorial_popl20 Require Export safety.

Section parametricity.
  Context `{heapG Σ}.

  Definition parametricity_I_sem_ty Σ (v : val) : sem_ty Σ :=
    SemTy (λ w, ⌜w = v⌝)%I.

  Lemma parametricity_I `{!heapPreG Σ} e (v : val) σ w es σ' :
    (∀ `{heapG Σ}, ∅ ⊨ e : ∀ A, A → A) →
    rtc erased_step ([e <_> v]%E, σ) (of_val w :: es, σ') → w = v.
  Proof.
    intros He.
    apply sem_gen_type_safety with (φ := λ u, u = v)=> ?.
    exists (parametricity_I_sem_ty Σ v). split.
    { by iIntros (?) "?". }
    iIntros (vs) "!# #Hvs".
    iPoseProof (He with "Hvs") as "He /=".
    wp_apply (wp_wand with "He").
    iIntros (u) "#Hu".
    wp_apply (wp_wand with "Hu"). iIntros (w') "Hw'". by iApply "Hw'".
  Qed.

  (** * Exercise (easy) *)
  (* REMOVE *) Definition parametricity_empty_sem_ty Σ : sem_ty Σ :=
    SemTy (λ w, False)%I.

  Lemma parametricity_empty `{!heapPreG Σ} e (v : val) σ w es σ' :
    (∀ `{heapG Σ}, ∅ ⊨ e : ∀ A, A) →
    rtc erased_step ([e <_>]%E, σ) (of_val w :: es, σ') →
    False.
  (* REMOVE *) Proof.
    intros He.
    change False with ((λ _, False) w).
    apply sem_gen_type_safety with (φ := λ _, False)=> ?.
    exists (parametricity_empty_sem_ty Σ). split.
    { by iIntros (?) "?". }
    iIntros (vs) "!# #Hvs".
    iPoseProof (He with "Hvs") as "He /=".
    wp_apply (wp_wand with "He").
    iIntros (u) "#Hu".
    iApply ("Hu" $! (parametricity_empty_sem_ty Σ)).
  Qed.
End parametricity.
