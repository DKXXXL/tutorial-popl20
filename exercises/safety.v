From iris.heap_lang Require Export adequacy.
From exercises Require Export fundamental.

(** * Semantic and syntactic type safety *)
(** We prove *semantic type safety*, which says that any _closed_ expression
that is semantically typed is safe, i.e., it does not crash. Based on this
theorem we then prove *syntactic type safety* as a corollary, i.e., any _closed_
syntactically well-typed program is safe. Semantic type safety is a consequence
of Iris's adequacy theorem, and syntactic type safety is a consequence of the
fundamental theorem together and semantic type safety. *)

(** ** Semantic type safety *)
(** Before proving semantic type safety, we first prove a stronger lemma. We
use this lemma in the file [parametricity.v] to prove parametricity properties.
This stronger lemma states that given a closed program [e], heap [σ], and a
_Coq_ predicate [φ : val → Prop], if there is a semantic type [A] such that [A]
implies [φ], and [e] is semantically typed at type [A], then we have
[adequate NotStuck e σ (λ v σ, φ v)].

The proposition [adequate NotStuck e σ (λ v σ, φ v)] (which is defined in the
Iris library) means that [e], starting in heap [σ] does not get stuck, and if
[e] reduces to a value [v], we have [φ v]. *)
Lemma sem_gen_type_safety `{!heapPreG Σ} e σ φ :
  (∀ `{!heapG Σ}, ∃ A : sem_ty Σ, (∀ v, A v -∗ ⌜φ v⌝) ∧ ⊢ ∅ ⊨ e : A) →
  adequate NotStuck e σ (λ v σ, φ v).
Proof.
  intros Hty. apply (heap_adequacy Σ NotStuck e σ)=> // ?.
  specialize (Hty _) as (A & HA & Hty).
  iStartProof. iDestruct (Hty $! ∅) as "#He".
  iSpecialize ("He" with "[]"); first by rewrite /env_sem_typed.
  rewrite subst_map_empty. iIntros "?". iApply (wp_wand with "He"); auto.
  by iIntros; iApply HA.
Qed.

(** The actual theorem for semantic type safety lemma states that semantically
typed closed programs do not get stuck. It is a simple consequence of the lemma
[sem_gen_type_safety] above. *)
Theorem sem_type_safety `{!heapPreG Σ} e σ es σ' e' :
  (∀ `{!heapG Σ}, ∃ A, ⊢ ∅ ⊨ e : A) →
  rtc erased_step ([e], σ) (es, σ') → e' ∈ es →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hty.
  apply sem_gen_type_safety with (φ := λ _, True)=> // ?.
  specialize (Hty _) as [A Hty]; eauto.
Qed.

(** ** Syntactic type safety *)
(** Syntactic type safety is a consequence of the fundamental theorem together
and semantic type safety. *)
Corollary type_safety e σ es σ' e' τ :
  (∅ ⊢ₜ e : τ) →
  rtc erased_step ([e], σ) (es, σ') → e' ∈ es →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hty. apply (sem_type_safety (Σ:=heapΣ))=> ?.
  exists (⟦ τ ⟧ []). rewrite -(interp_env_empty []).
  by apply fundamental.
Qed.
