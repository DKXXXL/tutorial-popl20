From iris.algebra Require Import auth.
From iris.base_logic Require Import lib.own.
From iris.proofmode Require Export tactics.

(** * Ghost theory for the [unsafe_ref_reuse] exercise *)
(** This file defines the ghost resources [two_state_auth] and [two_state_final]
using Iris's generic mechanism for ghost state. These resources satisfy the
following laws:

<<
  two_state_init:   |==> ∃ γ, two_state_auth γ false
  two_state_update: two_state_auth γ b ==∗ two_state_auth γ true ∗ two_state_final γ.
  two_state_agree:  two_state_auth γ b -∗ two_state_final γ -∗ ⌜b = true⌝.
>>
*)

Class two_stateG Σ := { two_state_inG :> inG Σ (authR (optionUR unitR)) }.
Definition two_stateΣ : gFunctors := #[GFunctor (authR (optionUR unitR))].

Instance subG_two_stateΣ {Σ} : subG two_stateΣ Σ → two_stateG Σ.
Proof. solve_inG. Qed.

Section two_state_ghost.
  Context `{!two_stateG Σ}.

  Definition two_state_auth (γ : gname) (b : bool) : iProp Σ :=
    own γ (● (if b then Some () else None)).

  Definition two_state_final (γ : gname) : iProp Σ :=
    own γ (◯ (Some ())).

  Lemma two_state_init : ⊢ |==> ∃ γ, two_state_auth γ false.
  Proof. iApply own_alloc. by apply auth_auth_valid. Qed.

  Lemma two_state_update γ b :
    two_state_auth γ b ==∗
    two_state_auth γ true ∗ two_state_final γ.
  Proof.
    iIntros "H".
    iMod (own_update _ _ (● Some () ⋅ ◯ Some ()) with "H") as "[$ $]"; last done.
    apply auth_update_alloc. destruct b.
    - by apply local_update_unital_discrete=> -[[]|].
    - by apply alloc_option_local_update.
  Qed.

  Global Instance two_state_auth_timeless γ b : Timeless (two_state_auth γ b).
  Proof. apply _. Qed.
  Global Instance two_state_final_timeless γ : Timeless (two_state_final γ).
  Proof. apply _. Qed.
  Global Instance two_state_final_persistent γ : Persistent (two_state_final γ).
  Proof. apply _. Qed.

  Lemma two_state_agree γ b :
    two_state_auth γ b -∗ two_state_final γ -∗ ⌜b = true⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hinc _]%auth_both_valid_discrete.
    apply option_included in Hinc as [|([]&[]&_&?&_)];
      destruct b; naive_solver.
  Qed.

  Typeclasses Opaque two_state_auth two_state_final.
End two_state_ghost.
