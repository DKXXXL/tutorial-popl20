From iris.algebra Require Import auth.
From iris.base_logic Require Import lib.own.
From iris.heap_lang.lib Require Import assert.
From tutorial_popl20 Require Export sem_typing safety.

Section exercises.
  Context `{heapG Σ}.

  Definition exercise1_prog : val := λ: <>, if: #true then #13 else #13 #37.

  Lemma exercise1 : ∅ ⊨ exercise1_prog : sem_ty_unit → sem_ty_int.
  Proof.
    iIntros (vs) "!# HΓ"; simpl.
    iApply wp_value.
    iIntros "!#" (w) "Hw".
    wp_lam.
    wp_if.
    rewrite /sem_ty_car /=.
    by iExists 13.
  Qed.

  Definition exercise2_prog : val :=
    λ: <>, let: "l" := ref #0 in "l" <- #true;; !"l".

  Lemma exercise2 : ∅ ⊨ exercise2_prog : sem_ty_unit → sem_ty_bool.
  Proof.
    iIntros (vs) "!# HΓ"; simpl.
    iApply wp_value.
    iIntros "!#" (v) "Hv".
    wp_lam.
    wp_alloc l as "Hl".
    wp_let.
    wp_store.
    wp_load.
    rewrite /sem_ty_car /=.
    by iExists true.
  Qed.

  Definition exercise3_prog : val :=
    λ: <>,
       let: "l" := ref #1 in
       ((λ: "x", if: "x" ≠ #0 then "l" <- "x" else #()),
        (λ: <>, assert: !"l" ≠ #0)).

  Lemma exercise3 :
    ∅ ⊨ exercise3_prog :
      sem_ty_unit → (sem_ty_int → sem_ty_unit) * (sem_ty_unit → sem_ty_unit).
  Proof.
    iIntros (vs) "!# HΓ"; simpl.
    iApply wp_value.
    iIntros "!#" (v) "Hv".
    wp_lam.
    wp_alloc l as "Hl".
    wp_let.
    iMod (inv_alloc (nroot .@ "ex3") _ (∃ n : Z, ⌜#n ≠ #0⌝ ∗ l ↦ #n) with "[Hl]")%I
      as "#Hinv".
    { by iNext; iExists 1; iFrame. }
    wp_pures.
    iExists _, _. iSplit; first done.
    iSplit.
    - iIntros "!#" (w) "Hw".
      iDestruct "Hw" as (n) "%".
      subst.
      wp_lam.
      wp_op.
      destruct (decide (#n = #0%Z)); first subst.
      + rewrite bool_decide_eq_true_2; last done.
        wp_op.
        wp_if.
        done.
      + rewrite bool_decide_eq_false_2; last done.
        wp_op.
        wp_if.
        iInv (nroot .@ "ex3") as "I" "Hcl".
        iDestruct "I" as (m) "[Hm Hl]".
        wp_store.
        iMod ("Hcl" with "[Hl]") as "_".
        { iNext. by iExists n; iFrame. }
        iModIntro.
        done.
    - iIntros "!#" (w) "Hw".
      wp_lam.
      wp_pures.
      iApply wp_assert.
      wp_bind (! _)%E.
      iInv (nroot .@ "ex3") as "I" "Hcl".
      iDestruct "I" as (m) "[#Hm Hl]".
      wp_load.
      iMod ("Hcl" with "[Hl]") as "_".
      { iNext. by iExists _; iFrame. }
      iModIntro.
      iDestruct "Hm" as %Hm.
      wp_op.
      rewrite bool_decide_eq_false_2; last done.
      wp_op.
      done.
  Qed.

  Definition exercise4_prog : val :=
    λ: <>, let: "l" := ref #0 in λ: <>, "l" <- #true;; !"l".

  Definition exercise4_ghost_auth `{!inG Σ (authUR (optionUR unitR))}
             γ (o : option unit) := own γ (● o).

  Definition exercise4_ghost_frag `{!inG Σ (authUR (optionUR unitR))}
             γ (o : option unit) := own γ (◯ o).

  Lemma exercise4_ghost_init `{!inG Σ (authUR (optionUR unitR))} :
    (|==> ∃ γ, exercise4_ghost_auth γ None)%I.
  Proof.
    iApply own_alloc.
    by apply auth_auth_valid.
  Qed.

  Lemma exercise4_ghost_update `{!inG Σ (authUR (optionUR unitR))} γ :
    exercise4_ghost_auth γ None ==∗
    exercise4_ghost_auth γ (Some ()) ∗ exercise4_ghost_frag γ (Some ()).
  Proof.
    iIntros "H".
    iMod (own_update _ _ (● Some () ⋅ ◯ Some ()) with "H") as
        "[$ $]"; last done.
    apply auth_update_alloc.
    by apply alloc_option_local_update.
  Qed.

  Global Instance exercise4_ghost_frag_persistent
         `{!inG Σ (authUR (optionUR unitR))} γ o :
    Persistent (exercise4_ghost_frag γ o).
  Proof. apply _. Qed.

  Lemma exercise4_ghost_observe `{!inG Σ (authUR (optionUR unitR))} γ o :
    exercise4_ghost_auth γ o ==∗
    exercise4_ghost_auth γ o ∗ exercise4_ghost_frag γ o.
  Proof.
    iIntros "H".
    iMod (own_update _ _ (● o ⋅ ◯ o) with "H") as "[$ $]"; last done.
    apply auth_update_alloc.
    apply local_update_unital_discrete.
    intros ?. rewrite left_id. intros ? <-; split; first done.
    by destruct o as [[]|].
  Qed.

  Lemma exercise4_ghost_agree `{!inG Σ (authUR (optionUR unitR))} γ o u :
    exercise4_ghost_auth γ o -∗ exercise4_ghost_frag γ (Some u) -∗ ⌜o = Some u⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hinc _]%auth_both_valid.
    iPureIntro.
    apply option_included in Hinc as [|(?&?&?&?&?)]; first done.
    by destruct o as [[]|]; destruct u; simplify_eq.
  Qed.

  Lemma exercise4 `{!inG Σ (authUR (optionUR unitR))} :
    ∅ ⊨ exercise4_prog : sem_ty_unit → (sem_ty_unit → sem_ty_bool).
  Proof.
    iIntros (vs) "!# HΓ"; simpl.
    iApply wp_value.
    iIntros "!#" (v) "Hv".
    wp_lam.
    wp_alloc l as "Hl".
    iMod exercise4_ghost_init as (γ) "Ho".
    iMod (inv_alloc
            (nroot .@ "ex4") _
            (∃ o v, exercise4_ghost_auth γ o ∗ l ↦ v ∗
                  ⌜match o with
                  | None => v = #0
                  | Some _ => v = #true
                  end⌝
         )%I with "[Hl Ho]") as "#Hinv".
    { iNext. by iExists None, _; iFrame. }
    wp_pures.
    iIntros "!#" (w) "Hw".
    wp_lam.
    wp_bind (_ <- _)%E.
    iInv (nroot .@ "ex4") as "I" "Hcl".
    iDestruct "I" as (o x) "(Ho&Hl&Hx)".
    wp_store.
    destruct o.
    - iMod (exercise4_ghost_observe with "Ho") as "[Ho #Hf]".
      iMod ("Hcl" with "[Hl Ho]") as "_".
      { iNext. by iExists _, _; iFrame. }
      iModIntro.
      wp_pures.
      iDestruct "Hx" as %->.
      iInv (nroot .@ "ex4") as "I" "Hcl".
      iDestruct "I" as (o x) "(Ho&Hl&Hx)".
      wp_load.
      iDestruct (exercise4_ghost_agree with "Ho Hf") as %->.
      iDestruct "Hx" as %->.
      iMod ("Hcl" with "[Hl Ho]") as "_".
      { iNext. by iExists _, _; iFrame. }
      iModIntro.
      rewrite /sem_ty_car /=.
      by iExists _.
    - iMod (exercise4_ghost_update with "Ho") as "[Ho #Hf]".
      iMod ("Hcl" with "[Hl Ho]") as "_".
      { iNext. by iExists _, _; iFrame. }
      iModIntro.
      wp_pures.
      iDestruct "Hx" as %->.
      iInv (nroot .@ "ex4") as "I" "Hcl".
      iDestruct "I" as (o x) "(Ho&Hl&Hx)".
      wp_load.
      iDestruct (exercise4_ghost_agree with "Ho Hf") as %->.
      iDestruct "Hx" as %->.
      iMod ("Hcl" with "[Hl Ho]") as "_".
      { iNext. by iExists _, _; iFrame. }
      iModIntro.
      rewrite /sem_ty_car /=.
      by iExists _.
  Qed.

End exercises.

Definition exercise5_prog (e : expr) (v : val) : expr := e ! v.

Definition exercise5_sem_ty Σ (v : val) : sem_ty Σ := SemTy (λ w, ⌜w = v⌝)%I.

Lemma exercise5 `{!heapPreG Σ} e v σ w es σ' :
  (∀ `{heapG Σ}, ∅ ⊨ e : ∀ A, A → A) →
  rtc erased_step ([exercise5_prog e v : expr], σ) (of_val w :: es, σ') → w = v.
Proof.
  intros He.
  apply sem_type_safety with (φ := λ u, u = v).
  intros ?.
  exists (exercise5_sem_ty Σ v).
  split.
  - by iIntros (?) "?".
  - iIntros (vs) "!# #Hvs".
    iDestruct (env_sem_typed_empty with "Hvs") as %->.
    iPoseProof (He with "Hvs") as "H"; simpl.
    rewrite subst_map_empty.
    wp_bind e.
    iApply wp_wand_r; iSplitL; first eauto.
    iIntros (u) "#Hu".
    iSpecialize ("Hu" $! (exercise5_sem_ty Σ v)).
    wp_bind (u #()).
    iApply wp_wand_r; iSplitL; first eauto.
    iIntros (u') "Hu'".
    iApply "Hu'".
    done.
Qed.
