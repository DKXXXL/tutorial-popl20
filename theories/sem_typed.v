From tutorial_popl20 Require Export sem_type_formers.

(** * Here we define the semantic typing judgment. *)

(** We define the judgment [Γ ⊨ e : A] for semantic typing of the
    expression [e] at semantic type [A], assuming that free variables
    in [e] belong to the semantic types described by [Γ]. This notion
    is defined as follows:

    - We define the semantic typing relation [env_sem_typed] for
      typing contexts: An environments (mappings from free variables
      to values) [vs] is in the semantic type for a typing context
      [Γ], [env_sem_typed Γ vs], if for any free variable [x], [vs(x)]
      is in the semantic type [Γ(x)].

    - The semantic typing judgment [Γ ⊨ e : A] holds if for any
      environment [vs] such that [env_sem_typed Γ vs] we have that
      [subst_map vs e] is an expression in the semantics of type [A],
      i.e., [WP subst_map vs e {{ A }}] holds. *)


(** The semantic type for the typing context (environment). *)
Definition env_sem_typed `{!heapG Σ} (Γ : gmap string (sem_ty Σ))
    (vs : gmap string val) : iProp Σ :=
  ([∗ map] i ↦ A;v ∈ Γ; vs, sem_ty_car A v)%I.
Instance: Params (@env_sem_typed) 2 := {}.

(** The semantics typing judgment. *)
Definition sem_typed `{!heapG Σ}
    (Γ : gmap string (sem_ty Σ)) (e : expr) (A : sem_ty Σ) : iProp Σ :=
  tc_opaque (□ ∀ vs,
    env_sem_typed Γ vs -∗ WP subst_map vs e {{ A }})%I.
Instance: Params (@sem_typed) 2 := {}.
Notation "Γ ⊨ e : A" := (sem_typed Γ e A)
  (at level 74, e, A at next level) : bi_scope.

Definition sem_val_typed `{!heapG Σ} (v : val) (A : sem_ty Σ) : iProp Σ :=
  tc_opaque (A v).
Instance: Params (@sem_val_typed) 3 := {}.
Notation "⊨ᵥ v : A" := (sem_val_typed v A)
  (at level 20, v, A at next level) : bi_scope.
Arguments sem_val_typed : simpl never.

(** A few useful lemmas about the semantic typing judgment. The first
few lemmas involving [Proper]ness are boilerplate required for supporting setoid
rewriting. *)
Section sem_typed.
  Context `{!heapG Σ}.
  Implicit Types A B : sem_ty Σ.
  Implicit Types C : sem_ty Σ → sem_ty Σ.

  Global Instance env_sem_typed_ne n :
    Proper (dist n ==> (=) ==> dist n) (@env_sem_typed Σ _).
  Proof.
    intros Γ1 Γ2 HΓ ρ ? <-.
    apply big_sepM2_ne_2=> // k A1 v1 A2 v2 _ _ HA _ _ /discrete_iff / leibniz_equiv_iff ->.
    by apply HA.
  Qed.
  Global Instance env_sem_typed_proper :
    Proper ((≡) ==> (=) ==> (≡)) (@env_sem_typed Σ _).
  Proof. intros Γ1 Γ2 HΓ ρ ? <-. apply equiv_dist=> n. f_equiv. by rewrite HΓ. Qed.

  Global Instance sem_typed_ne n :
    Proper (dist n ==> (=) ==> dist n ==> dist n) (@sem_typed Σ _).
  Proof. solve_proper. Qed.
  Global Instance sem_typed_proper :
    Proper ((≡) ==> (=) ==> (≡) ==> (≡)) (@sem_typed Σ _).
  Proof. solve_proper. Qed.

  Global Instance sem_typed_persistent Γ e A : Persistent (Γ ⊨ e : A).
  Proof. rewrite /sem_typed /=. apply _. Qed.

  Global Instance sem_val_typed_ne v : NonExpansive (@sem_val_typed Σ _ v).
  Proof. solve_proper. Qed.
  Global Instance sem_val_typed_proper v :
    Proper ((≡) ==> (≡)) (@sem_val_typed Σ _ v).
  Proof. solve_proper. Qed.

  Global Instance sem_val_typed_persistent v A : Persistent (⊨ᵥ v : A).
  Proof. rewrite /sem_val_typed /=. apply _. Qed.

  (* Environments *)
  Lemma env_sem_typed_lookup Γ vs x A :
    Γ !! x = Some A →
    env_sem_typed Γ vs -∗ ∃ v, ⌜ vs !! x = Some v ⌝ ∧ A v.
  Proof.
    iIntros (HΓx) "HΓ". rewrite /env_sem_typed.
    by iApply (big_sepM2_lookup_1 with "HΓ").
  Qed.
  Lemma env_sem_typed_insert Γ vs x A v :
    A v -∗ env_sem_typed Γ vs -∗
    env_sem_typed (binder_insert x A Γ) (binder_insert x v vs).
  Proof.
    destruct x as [|x]=> /=; first by auto. rewrite /env_sem_typed.
    iIntros "#HA #HΓ". by iApply (big_sepM2_insert_2 with "[] HΓ").
  Qed.

  Lemma env_sem_typed_empty : env_sem_typed ∅ ∅.
  Proof. iIntros "". by rewrite /env_sem_typed. Qed.
  Lemma env_sem_typed_empty_l_inv vs : env_sem_typed ∅ vs -∗ ⌜vs = ∅⌝.
  Proof. by iIntros "?"; iApply big_sepM2_empty_r. Qed.
End sem_typed.
