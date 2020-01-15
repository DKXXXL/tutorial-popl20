From tutorial_popl20 Require Export sem_typing.
From iris.heap_lang.lib Require Import assert.
From tutorial_popl20 Require Export symbol_ghost.

(* Semantic typing of a symbol ADT (taken from Dreyer's POPL'18 talk) *)
Definition symbol_adt_inc : val := λ: "x" <>, FAA "x" #1.
Definition symbol_adt_check : val := λ: "x" "y", assert: "y" < !"x".
Definition symbol_adt : val := λ: <>,
  let: "x" := Alloc #0 in (symbol_adt_inc "x", symbol_adt_check "x").

Definition symbol_adt_ty `{heapG Σ} : sem_ty Σ :=
  (() → ∃ A, (() → A) * (A → ()))%sem_ty.

Section sem_typed_symbol_adt.
  Context `{heapG Σ, symbolG Σ}.

  Definition symbol_adtN := nroot .@ "symbol_adt".

  Definition symbol_inv (γ : gname) (l : loc) : iProp Σ :=
    (∃ n : nat, l ↦ #n ∗ counter γ n)%I.

  Definition sem_ty_symbol (γ : gname) : sem_ty Σ := SemTy (λ w,
    ∃ n : nat, ⌜w = #n⌝ ∧ symbol γ n)%I.

  Lemma sem_typed_symbol_adt Γ : Γ ⊨ symbol_adt : symbol_adt_ty.
  Proof.
    iIntros (vs) "!# _ /=". iApply wp_value.
    iIntros "!#" (v ->). wp_lam. wp_alloc l as "Hl"; wp_pures.
    iMod (counter_alloc 0) as (γ) "Hc".
    iMod (inv_alloc symbol_adtN _ (symbol_inv γ l) with "[Hl Hc]") as "#?".
    { iExists 0%nat. by iFrame. }
    do 2 (wp_lam; wp_pures).
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
