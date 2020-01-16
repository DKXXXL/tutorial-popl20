From iris.algebra Require Import auth.
From iris.base_logic Require Import lib.own.
From iris.heap_lang.lib Require Import assert.
From tutorial_popl20 Require Export sem_typing safety.

Section exercises.
  Context `{heapG Σ}.

  (* Easy *)
  Definition exercise1_prog : val := λ: <>,
    if: #true then #13 else #13 #37.

  Lemma exercise1 : ∅ ⊨ exercise1_prog : () → sem_ty_int.
  Proof.
    iIntros (vs) "!# HΓ"; simpl.
    iApply wp_value.
    iIntros "!#" (? ->).
    wp_lam.
    wp_if.
    rewrite /sem_ty_car /=.
    by iExists 13.
  Qed.

  (* Easy *)
  Definition exercise2_prog : val := λ: <>,
    let: "l" := ref #0 in "l" <- #true;; !"l".

  Lemma exercise2 : ∅ ⊨ exercise2_prog : () → sem_ty_bool.
  Proof.
    iIntros (vs) "!# HΓ"; simpl.
    iApply wp_value.
    iIntros "!#" (? ->).
    wp_lam.
    wp_alloc l as "Hl".
    wp_let.
    wp_store.
    wp_load.
    rewrite /sem_ty_car /=.
    by iExists true.
  Qed.

  (* Moderate *)
  Definition exercise3_prog : val := λ: <>,
    let: "l" := ref #1 in
    ((λ: "x", if: "x" ≠ #0 then "l" <- "x" else #()),
     (λ: <>, assert: !"l" ≠ #0)).

  Lemma exercise3 : ∅ ⊨ exercise3_prog : () → (sem_ty_int → ()) * (() → ()).
  Proof.
    iIntros (vs) "!# HΓ"; simpl.
    iApply wp_value.
    iIntros "!#" (? ->).
    wp_lam.
    wp_alloc l as "Hl".
    wp_let.
    pose (I := (∃ n : Z, ⌜#n ≠ #0⌝ ∗ l ↦ #n)%I).
    iMod (inv_alloc (nroot .@ "exercise3") _ I with "[Hl]")%I as "#Hinv".
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
        iInv (nroot .@ "exercise3") as (m) ">[% Hl]".
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
      iInv (nroot .@ "exercise3") as (m) ">[% Hl]".
      wp_load.
      iModIntro. iSplitL "Hl".
      { iExists m; auto. }
      wp_op.
      rewrite bool_decide_eq_false_2; last done.
      by wp_op.
  Qed.

  Definition exercise4_prog : val :=
    λ: <>, let: "l" := ref #0 in λ: <>, "l" <- #true;; !"l".

  Section exercise4.
    Context `{!inG Σ (authUR (optionUR unitR))}.

    Definition exercise4_auth (γ : gname) (b : bool) : iProp Σ :=
      own γ (● (if b then Some () else None)).

    Definition exercise4_final (γ : gname) : iProp Σ :=
      own γ (◯ (Some ())).

    Lemma exercise4_ghost_init : (|==> ∃ γ, exercise4_auth γ false)%I.
    Proof. iApply own_alloc. by apply auth_auth_valid. Qed.

    Lemma exercise4_ghost_update γ b :
      exercise4_auth γ b ==∗
      exercise4_auth γ true ∗ exercise4_final γ.
    Proof.
      iIntros "H".
      iMod (own_update _ _ (● Some () ⋅ ◯ Some ()) with "H") as "[$ $]"; last done.
      apply auth_update_alloc. destruct b.
      - by apply local_update_unital_discrete=> -[[]|].
      - by apply alloc_option_local_update.
    Qed.

    Global Instance exercise4_auth_timeless γ b : Timeless (exercise4_auth γ b).
    Proof. apply _. Qed.
    Global Instance exercise4_final_timeless γ : Timeless (exercise4_final γ).
    Proof. apply _. Qed.
    Global Instance exercise4_final_persistent γ : Persistent (exercise4_final γ).
    Proof. apply _. Qed.

    Lemma exercise4_ghost_agree γ b :
      exercise4_auth γ b -∗ exercise4_final γ -∗ ⌜b = true⌝.
    Proof.
      iIntros "H1 H2".
      iDestruct (own_valid_2 with "H1 H2") as %[Hinc _]%auth_both_valid.
      apply option_included in Hinc as [|([]&[]&_&?&_)];
        destruct b; naive_solver.
    Qed.

    Typeclasses Opaque exercise4_auth exercise4_final.

    Lemma exercise4 :
      ∅ ⊨ exercise4_prog : sem_ty_unit → (sem_ty_unit → sem_ty_bool).
    Proof.
      iIntros (vs) "!# HΓ"; simpl.
      iApply wp_value.
      iIntros "!#" (? ->).
      wp_lam.
      wp_alloc l as "Hl".
      iMod exercise4_ghost_init as (γ) "Ho".
      pose (I := (∃ b, exercise4_auth γ b ∗
        l ↦ (if b then #true else #0))%I).
      iMod (inv_alloc (nroot .@ "exercise4") _ I with "[Hl Ho]") as "#Hinv".
      { iNext. iExists false. iFrame. }
      wp_pures.
      iIntros "!#" (? ->).
      wp_lam.
      (* Need because of atomic expression *)
      wp_bind (_ <- _)%E.
      iInv (nroot .@ "exercise4") as (o) ">[Ho Hl]".
      wp_store.
      iMod (exercise4_ghost_update with "Ho") as "[Ho Hf]".
      iModIntro. iSplitL "Hl Ho".
      { iNext. iExists true. iFrame. }
      wp_pures.
      iInv (nroot .@ "exercise4") as (o') ">[Ho Hl]".
      iDestruct (exercise4_ghost_agree with "Ho Hf") as %->.
      wp_load.
      iModIntro. iSplitL "Hl Ho".
      { iNext. iExists true. iFrame. }
      rewrite /sem_ty_car /=. by iExists _.
    Qed.
  End exercise4.
End exercises.

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
