From tutorial_popl20 Require Export safety.

Section parametricity.
  Context `{heapG Σ}.

  Definition identity_param_sem_ty Σ (v : val) : sem_ty Σ :=
    SemTy (λ w, ⌜w = v⌝)%I.

  Lemma identity_param `{!heapPreG Σ} e (v : val) σ w es σ' :
    (∀ `{heapG Σ}, ∅ ⊨ e : ∀ A, A → A) →
    rtc erased_step ([e <_> v]%E, σ) (of_val w :: es, σ') → w = v.
  Proof.
    intros He.
    apply sem_gen_type_safety with (φ := λ u, u = v)=> ?.
    exists (identity_param_sem_ty Σ v). split.
    { by iIntros (?) "?". }
    iIntros (vs) "!# #Hvs".
    iPoseProof (He with "Hvs") as "He /=".
    wp_apply (wp_wand with "He").
    iIntros (u) "#Hu".
    iSpecialize ("Hu" $! (identity_param_sem_ty Σ v)).
    wp_apply (wp_wand with "Hu"). iIntros (w') "Hw'". by iApply "Hw'".
  Qed.

  (* REMOVE *) Definition empty_type_param_sem_ty Σ : sem_ty Σ :=
    SemTy (λ w, False)%I.

  Lemma empty_type_param `{!heapPreG Σ} e (v : val) σ w es σ' :
    (∀ `{heapG Σ}, ∅ ⊨ e : ∀ A, A) →
    rtc erased_step ([e <_>]%E, σ) (of_val w :: es, σ') →
    False.
  (* REMOVE *) Proof.
    intros He.
    change False with ((λ _, False) w).
    apply sem_gen_type_safety with (φ := λ _, False)=> ?.
    exists (empty_type_param_sem_ty Σ). split.
    { by iIntros (?) "?". }
    iIntros (vs) "!# #Hvs".
    iPoseProof (He with "Hvs") as "He /=".
    wp_apply (wp_wand with "He").
    iIntros (u) "#Hu".
    iApply ("Hu" $! (empty_type_param_sem_ty Σ)).
  Qed.

  (* REMOVE *) Definition boolean_param_sem_ty Σ (v1 v2 : val) : sem_ty Σ :=
    SemTy (λ w, ⌜w = v1 ∨ w = v2⌝)%I.

  Lemma boolean_param `{!heapPreG Σ} e (v1 v2 : val) σ w es σ' :
    (∀ `{heapG Σ}, ∅ ⊨ e : ∀ A, A → A → A) →
    rtc erased_step ([e <_> v1 v2]%E, σ) (of_val w :: es, σ') → w = v1 ∨ w = v2.
  (* REMOVE *) Proof.
    intros He.
    apply sem_gen_type_safety with (φ := λ w, w = v1 ∨ w = v2)=> ?.
    exists (boolean_param_sem_ty Σ v1 v2). split.
    { by iIntros (?) "?". }
    iIntros (vs) "!# #Hvs".
    iPoseProof (He with "Hvs") as "He /=".
    wp_apply (wp_wand with "He").
    iIntros (u) "#Hu".
    iSpecialize ("Hu" $! (boolean_param_sem_ty Σ v1 v2)).
    wp_apply (wp_wand with "Hu"). iIntros (w') "#Hw'".
    iSpecialize ("Hw'" $! v1 with "[]"); first by eauto.
    wp_apply (wp_wand with "Hw'").
    iIntros (w'') "#Hw''".
    by iApply ("Hw''" $! v2 with "[]"); eauto.
  Qed.

  (* REMOVE *) Definition nat_param_sem_ty Σ : sem_ty Σ :=
    SemTy (λ w, ∃ n : nat, ⌜w = #n⌝)%I.

  Lemma nat_param `{!heapPreG Σ} e σ w es σ' :
    (∀ `{heapG Σ}, ∅ ⊨ e : ∀ A, (A → A) → A → A) →
    rtc erased_step ([e <_> (λ: "n", "n" + #1)%V #0]%E, σ)
      (of_val w :: es, σ') → ∃ n : nat, w = #n.
  (* REMOVE *) Proof.
    intros He.
    apply sem_gen_type_safety with (φ := λ w, ∃ n : nat, w = #n)=> ?.
    exists (nat_param_sem_ty Σ). split.
    { iIntros (?). iDestruct 1 as (?) "%". eauto. }
    iIntros (vs) "!# #Hvs".
    iPoseProof (He with "Hvs") as "He /=".
    wp_apply (wp_wand with "He").
    iIntros (u) "#Hu".
    iSpecialize ("Hu" $! (nat_param_sem_ty Σ)).
    wp_apply (wp_wand with "Hu"). iIntros (w') "#Hw'".
    iSpecialize ("Hw'" $! (λ: "n", "n" + #1)%V with "[]").
    { iIntros "!#" (? [n ->]).
      wp_lam.
      wp_op.
      iExists (n + 1)%nat.
      by rewrite Nat2Z.inj_add. }
    wp_apply (wp_wand with "Hw'").
    iIntros (w'') "#Hw''".
    iApply ("Hw''" $! #0 with "[]"); eauto.
    by iExists 0%nat.
  Qed.

  (* REMOVE *) Definition strong_nat_param_sem_ty {A Σ} (Ψ : A → sem_ty Σ) : sem_ty Σ :=
    SemTy (λ w, ∃ x : A, Ψ x w)%I.

  Lemma strong_nat_param `{!heapPreG Σ} e σ w es σ' (vf vz : val) ψ:
    (∀ `{heapG Σ}, ∃ (Ψ : nat → sem_ty Σ),
      (∅ ⊨ e : ∀ A, (A → A) → A → A) ∧
      (∀ n w, {{{ Ψ n w }}} vf w {{{ w', RET w'; Ψ (S n) w' }}}) ∧
      (Ψ 0%nat vz) ∧
      (∀ n w, Ψ n w -∗ ⌜ψ n w⌝)) →
    rtc erased_step ([e <_> vf vz]%E, σ) (of_val w :: es, σ') → ∃ n : nat, ψ n w.
  (* REMOVE *) Proof.
    intros He.
    apply sem_gen_type_safety with (φ := λ w, ∃ n, ψ n w)=> ?.
    exists (strong_nat_param_sem_ty (λ n : nat, SemTy (λ w, ⌜ψ n w⌝)%I)). split.
    { iIntros (v [n ?]); eauto. }
    specialize (He _) as (Ψ & He & Hvf & Hvz & Hψ).
    iIntros (vs) "!# #Hvs".
    iPoseProof (He with "Hvs") as "He /=".
    wp_apply (wp_wand with "He").
    iIntros (u) "#Hu".
    iSpecialize ("Hu" $! (strong_nat_param_sem_ty Ψ)).
    wp_apply (wp_wand with "Hu"). iIntros (w') "#Hw'".
    iSpecialize ("Hw'" $! vf with "[]").
    { iIntros "!#" (u') "Hu'".
      iDestruct "Hu'"as (k) "Hu'".
      iApply (Hvf with "Hu'").
      iIntros "!>" (u'') "Hu''".
      by iExists _. }
    wp_apply (wp_wand with "Hw'").
    iIntros (w'') "#Hw''".
    iApply wp_wand.
    { iApply ("Hw''" $! vz with "[]"); eauto.
      iExists 0%nat.
      iApply Hvz. }
    iIntros (v).
    iDestruct 1 as (k) "Hv".
    iExists k.
    by iApply Hψ.
  Qed.
End parametricity.
