From solutions Require Export sem_typed.
From solutions Require Import symbol_ghost two_state_ghost.

Section unsafe.
  Context `{!heapG Σ}.

  (** Recall the following function we defined in the file [language.v]:
  <<
  Definition unsafe_pure : val := λ: <>,
    if: #true then #13 else #13 #37.
  >>
  *)
  Lemma sem_typed_unsafe_pure : (∅ ⊨ unsafe_pure : (() → sem_ty_int))%I.
  Proof.
    iIntros (vs) "!# HΓ /=". iApply wp_value.
    iIntros "!#" (? ->). wp_lam. wp_if.
    rewrite /sem_ty_car /=.
    by iExists 13.
  Qed.

  (** * Exercise (unsafe_ref, easy) *)
  (** Recall the following function we defined in the file [language.v]:
  <<
  Definition unsafe_ref : val := λ: <>,
    let: "l" := ref #0 in "l" <- #true;; !"l".
  >> *)
  Lemma sem_typed_unsafe_ref : (∅ ⊨ unsafe_ref : (() → sem_ty_bool))%I.
  Proof.
    iIntros (vs) "!# HΓ /=". iApply wp_value.
    iIntros "!#" (? ->). wp_lam.
    wp_alloc l as "Hl".
    wp_store. wp_load.
    rewrite /sem_ty_car /=.
    by iExists true.
  Qed.

  (** * Exercise (unsafe_ref_ne_0, moderate) *)
  Definition unsafe_ref_ne_0 : val := λ: <>,
    let: "l" := ref #1 in
    ((λ: "x", if: "x" ≠ #0 then "l" <- "x" else #()),
     (λ: <>, assert: !"l" ≠ #0)).

  Lemma sem_typed_unsafe_ref_ne_0 :
    (∅ ⊨ unsafe_ref_ne_0 : (() → (sem_ty_int → ()) * (() → ())))%I.
  Proof.
    iIntros (vs) "!# HΓ /=". iApply wp_value.
    iIntros "!#" (? ->).
    wp_lam. wp_alloc l as "Hl". wp_let.
    pose (I := (∃ n : Z, ⌜#n ≠ #0⌝ ∗ l ↦ #n)%I).
    iMod (inv_alloc (nroot .@ "inv") _ I with "[Hl]")%I as "#Hinv".
    { by iNext; iExists 1; iFrame. }
    wp_pures.
    iExists _, _. iSplit; first done.
    iSplit.
    - iIntros "!#" (? [n ->]).
      wp_lam.
      wp_op.
      destruct (decide (n = 0%Z)); simplify_eq/=.
      + wp_op.
        wp_if.
        done.
      + rewrite bool_decide_eq_false_2; last congruence.
        wp_op.
        wp_if.
        iInv (nroot .@ "inv") as (m) ">[% Hl]".
        wp_store.
        iModIntro. iSplit.
        * iExists n; auto with congruence.
        * done.
    - iIntros "!#" (? ->).
      wp_lam.
      wp_pures.
      iApply wp_assert.
      (* Need because of atomic expression *)
      wp_bind (! _)%E.
      iInv (nroot .@ "inv") as (m) ">[% Hl]".
      wp_load.
      iModIntro. iSplitL "Hl".
      { iExists m; auto. }
      wp_op.
      rewrite bool_decide_eq_false_2; last done.
      by wp_op.
  Qed.

  (** * Exercise (unsafe_ref_reuse, hard) *)
  Definition unsafe_ref_reuse : val :=
    λ: <>, let: "l" := ref #0 in λ: <>, "l" <- #true;; !"l".

  Lemma sem_typed_unsafe_ref_reuse `{!two_stateG Σ}:
    (∅ ⊨ unsafe_ref_reuse : (() → (() → sem_ty_bool)))%I.
  Proof.
    iIntros (vs) "!# HΓ /=". iApply wp_value.
    iIntros "!#" (? ->). wp_lam.
    wp_alloc l as "Hl".
    iMod two_state_init as (γ) "Ho".
    pose (I := (∃ b, two_state_auth γ b ∗ l ↦ (if b then #true else #0))%I).
    iMod (inv_alloc (nroot .@ "inv") _ I with "[Hl Ho]") as "#Hinv".
    { iNext. iExists false. iFrame. }
    wp_pures.
    iIntros "!#" (? ->).
    wp_lam.
    (* Need because of atomic expression *)
    wp_bind (_ <- _)%E.
    iInv (nroot .@ "inv") as (o) ">[Ho Hl]".
    wp_store.
    iMod (two_state_update with "Ho") as "[Ho Hf]".
    iModIntro. iSplitL "Hl Ho".
    { iNext. iExists true. iFrame. }
    wp_pures.
    iInv (nroot .@ "inv") as (o') ">[Ho Hl]".
    iDestruct (two_state_agree with "Ho Hf") as %->.
    wp_load.
    iModIntro. iSplitL "Hl Ho".
    { iNext. iExists true. iFrame. }
    rewrite /sem_ty_car /=. by iExists _.
  Qed.

  (** * Exercise (unsafe_symbol_adt, hard) *)
  (** Semantic typing of a symbol ADT (taken from Dreyer's POPL'18 talk) *)
  Definition symbol_adt_inc : val := λ: "x" <>, FAA "x" #1.
  Definition symbol_adt_check : val := λ: "x" "y", assert: "y" < !"x".
  Definition symbol_adt : val := λ: <>,
    let: "x" := Alloc #0 in
    pack: (symbol_adt_inc "x", symbol_adt_check "x").

  Definition symbol_adt_ty : sem_ty Σ :=
    (() → ∃ A, (() → A) * (A → ())).

  Section sem_typed_symbol_adt.
    Context `{!symbolG Σ}.

    Definition symbol_adtN := nroot .@ "symbol_adt".

    Definition symbol_inv (γ : gname) (l : loc) : iProp Σ :=
      (∃ n : nat, l ↦ #n ∗ counter γ n)%I.

    Definition sem_ty_symbol (γ : gname) : sem_ty Σ := SemTy (λ w,
      ∃ n : nat, ⌜w = #n⌝ ∧ symbol γ n)%I.

    Lemma sem_typed_symbol_adt Γ : (Γ ⊨ symbol_adt : symbol_adt_ty)%I.
    Proof.
      iIntros (vs) "!# _ /=". iApply wp_value.
      iIntros "!#" (v ->). wp_lam. wp_alloc l as "Hl"; wp_pures.
      iMod (counter_alloc 0) as (γ) "Hc".
      iMod (inv_alloc symbol_adtN _ (symbol_inv γ l) with "[Hl Hc]") as "#?".
      { iExists 0%nat. by iFrame. }
      do 2 (wp_lam; wp_pures). wp_lam.
      iExists (sem_ty_symbol γ), _, _; repeat iSplit=> //.
      - repeat rewrite /sem_ty_car /=. iIntros "!#" (? ->). wp_pures.
        iInv symbol_adtN as (n) ">[Hl Hc]". wp_faa.
        iMod (counter_inc with "Hc") as "[Hc #Hs]".
        iModIntro; iSplitL; last eauto.
        iExists (S n). rewrite Nat2Z.inj_succ -Z.add_1_r. iFrame.
      - repeat rewrite /sem_ty_car /=. iIntros "!#" (v).
        iDestruct 1 as (n ->) "#Hs". wp_pures. iApply wp_assert.
        wp_bind (!_)%E. iInv symbol_adtN as (n') ">[Hl Hc]". wp_load.
        iDestruct (symbol_obs with "Hc Hs") as %?. iModIntro. iSplitL.
        { iExists n'. iFrame. }
        wp_op. rewrite bool_decide_true; last lia. eauto.
    Qed.
  End sem_typed_symbol_adt.
End unsafe.
