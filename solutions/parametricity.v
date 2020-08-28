From solutions Require Export safety.

(** * Parametricity *)
Section parametricity.
  Context `{!heapG Σ}.

  (** * The polymorphic identity function *)
  Lemma identity_param `{!heapPreG Σ} e (v : val) σ w es σ' :
    (∀ `{!heapG Σ}, ⊢ ∅ ⊨ e : ∀ A, A → A) →
    rtc erased_step ([e <_> v]%E, σ) (of_val w :: es, σ') → w = v.
  Proof.
    intros He.
    apply sem_gen_type_safety with (φ := λ u, u = v)=> ?.
    pose (T := SemTy (λ w, ⌜w = v⌝)%I : sem_ty Σ).
    exists T. split.
    { by iIntros (?) "?". }
    iIntros (vs) "!# #Hvs".
    iPoseProof (He with "Hvs") as "He /=".
    wp_apply (wp_wand with "He").
    iIntros (u) "#Hu".
    iSpecialize ("Hu" $! T).
    wp_apply (wp_wand with "Hu"). iIntros (w') "Hw'". by iApply "Hw'".
  Qed.

  (** * Exercise (empty_type_param, easy) *)
  Lemma empty_type_param `{!heapPreG Σ} e (v : val) σ w es σ' :
    (∀ `{!heapG Σ}, ⊢ ∅ ⊨ e : ∀ A, A) →
    rtc erased_step ([e <_>]%E, σ) (of_val w :: es, σ') →
    False.
  Proof.
  (* BEGIN SOLUTION *)
    intros He.
    change False with ((λ _, False) w).
    apply sem_gen_type_safety with (φ := λ _, False)=> ?.
    pose (T := SemTy (λ _, False%I) : sem_ty Σ).
    exists T. split.
    { by iIntros (?) "?". }
    iIntros (vs) "!# #Hvs".
    iPoseProof (He with "Hvs") as "He /=".
    wp_apply (wp_wand with "He").
    iIntros (u) "#Hu".
    iApply ("Hu" $! T).
  Qed.
  (* END SOLUTION *)

  (** * Exercise (boolean_param, moderate) *)
  Lemma boolean_param `{!heapPreG Σ} e (v1 v2 : val) σ w es σ' :
    (∀ `{!heapG Σ}, ⊢ ∅ ⊨ e : ∀ A, A → A → A) →
    rtc erased_step ([e <_> v1 v2]%E, σ) (of_val w :: es, σ') → w = v1 ∨ w = v2.
  Proof.
  (* BEGIN SOLUTION *)
    intros He.
    apply sem_gen_type_safety with (φ := λ w, w = v1 ∨ w = v2)=> ?.
    pose (T := SemTy (λ w, ⌜w = v1 ∨ w = v2⌝)%I : sem_ty Σ).
    exists T. split.
    { by iIntros (?) "?". }
    iIntros (vs) "!# #Hvs".
    iPoseProof (He with "Hvs") as "He /=".
    wp_apply (wp_wand with "He").
    iIntros (u) "#Hu".
    iSpecialize ("Hu" $! T).
    wp_apply (wp_wand with "Hu"). iIntros (w') "#Hw'".
    iSpecialize ("Hw'" $! v1 with "[]"); first by iLeft.
    wp_apply (wp_wand with "Hw'").
    iIntros (w'') "#Hw''".
    iApply ("Hw''" $! v2). by iRight.
  Qed.
  (* END SOLUTION *)

  (** * Exercise (nat_param, hard) *)
  Lemma nat_param `{!heapPreG Σ} e σ w es σ' :
    (∀ `{!heapG Σ}, ⊢ ∅ ⊨ e : ∀ A, (A → A) → A → A) →
    rtc erased_step ([e <_> (λ: "n", "n" + #1)%V #0]%E, σ)
      (of_val w :: es, σ') → ∃ n : nat, w = #n.
  Proof.
  (* BEGIN SOLUTION *)
    intros He.
    apply sem_gen_type_safety with (φ := λ w, ∃ n : nat, w = #n)=> ?.
    set (T := SemTy (λ w, ∃ n : nat, ⌜w = #n⌝)%I : sem_ty Σ).
    exists T. split.
    { iIntros (?). iDestruct 1 as (?) "%". eauto. }
    iIntros (vs) "!# #Hvs".
    iPoseProof (He with "Hvs") as "He /=".
    wp_apply (wp_wand with "He").
    iIntros (u) "#Hu".
    iSpecialize ("Hu" $! T).
    wp_apply (wp_wand with "Hu"). iIntros (w') "#Hw'".
    iSpecialize ("Hw'" $! (λ: "n", "n" + #1)%V with "[]").
    { iIntros "!#" (? [n ->]). wp_pures.
      iExists (n + 1)%nat.
      by rewrite Nat2Z.inj_add. }
    wp_apply (wp_wand with "Hw'").
    iIntros (w'') "#Hw''".
    iApply ("Hw''" $! #0).
    by iExists 0%nat.
  Qed.
  (* END SOLUTION *)

  (** * Exercise (strong_nat_param, hard) *)
  Lemma strong_nat_param `{!heapPreG Σ} e σ w es σ' (vf vz : val) φ :
    (∀ `{!heapG Σ}, ∃ Φ : sem_ty Σ,
      (⊢ ∅ ⊨ e : ∀ A, (A → A) → A → A) ∧
      (∀ w, ⊢ {{{ Φ w }}} vf w {{{ w', RET w'; Φ w' }}}) ∧
      (⊢ Φ vz) ∧
      (∀ w, Φ w -∗ ⌜φ w⌝)) →
    rtc erased_step ([e <_> vf vz]%E, σ) (of_val w :: es, σ') → φ w.
  Proof.
  (* BEGIN SOLUTION *)
    intros He.
    apply sem_gen_type_safety with (φ0 := φ)=> ?.
    set (T := SemTy (λ w, ⌜ φ w ⌝)%I : sem_ty Σ).
    exists T. split; first done.
    specialize (He _) as (Φ & He & Hvf & Hvz & Hφ).
    iIntros (vs) "!# #Hvs".
    iPoseProof (He with "Hvs") as "He /=".
    wp_apply (wp_wand with "He").
    iIntros (u) "#Hu".
    iSpecialize ("Hu" $! Φ).
    wp_apply (wp_wand with "Hu"). iIntros (w') "#Hw'".
    iSpecialize ("Hw'" $! vf with "[]").
    { iIntros "!#" (u') "Hu'".
      iApply (Hvf with "Hu'"); auto. }
    wp_apply (wp_wand with "Hw'").
    iIntros (w'') "#Hw''".
    iApply wp_wand.
    { iApply "Hw''". iApply Hvz. }
    iIntros (v). by iApply Hφ.
  Qed.
  (* END SOLUTION *)
End parametricity.
