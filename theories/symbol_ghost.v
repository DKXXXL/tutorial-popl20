From iris.algebra Require Import auth.
From iris.base_logic Require Import lib.own.
From iris.proofmode Require Export tactics.

(* The required ghost theory *)
Class symbolG Σ := { symbol_inG :> inG Σ (authR mnatUR) }.
Definition symbolΣ : gFunctors := #[GFunctor (authR mnatUR)].

Instance subG_symbolΣ {Σ} : subG symbolΣ Σ → symbolG Σ.
Proof. solve_inG. Qed.

Section symbol_ghost.
  Context `{!symbolG Σ}.

  Definition counter (γ : gname) (n : nat) : iProp Σ := own γ (● (n : mnat)).
  Definition symbol (γ : gname) (n : nat) : iProp Σ := own γ (◯ (S n : mnat)).

  Global Instance counter_timeless γ n : Timeless (counter γ n).
  Proof. apply _. Qed.
  Global Instance symbol_timeless γ n : Timeless (symbol γ n).
  Proof. apply _. Qed.

  Lemma counter_exclusive γ n1 n2 : counter γ n1 -∗ counter γ n2 -∗ False.
  Proof.
    apply bi.wand_intro_r. rewrite -own_op own_valid /=. by iDestruct 1 as %[].
  Qed.
  Global Instance symbol_persistent γ n : Persistent (symbol γ n).
  Proof. apply _. Qed.

  Lemma counter_alloc n : (|==> ∃ γ, counter γ n)%I.
  Proof.
    iMod (own_alloc (● (n:mnat) ⋅ ◯ (n:mnat))) as (γ) "[Hγ Hγf]";
      first by apply auth_both_valid.
    iExists γ. by iFrame.
  Qed.

  Lemma counter_inc γ n : counter γ n ==∗ counter γ (S n) ∗ symbol γ n.
  Proof.
    rewrite -own_op.
    apply own_update, auth_update_alloc, mnat_local_update. omega.
  Qed.

  Lemma symbol_obs γ s n : counter γ n -∗ symbol γ s -∗ ⌜(s < n)%nat⌝.
  Proof.
    iIntros "Hc Hs".
    iDestruct (own_valid_2 with "Hc Hs") as %[?%mnat_included _]%auth_both_valid.
    iPureIntro. omega.
  Qed.
End symbol_ghost.

Typeclasses Opaque counter symbol.
