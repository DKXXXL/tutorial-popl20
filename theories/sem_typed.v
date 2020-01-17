From tutorial_popl20 Require Export sem_type_formers.

(* The semantic typing judgment *)
Definition env_sem_typed `{heapG Σ} (Γ : gmap string (sem_ty Σ))
    (vs : gmap string val) : iProp Σ :=
  ([∗ map] i ↦ A;v ∈ Γ; vs, sem_ty_car A v)%I.
Instance: Params (@env_sem_typed) 2 := {}.
Definition sem_typed `{heapG Σ}
    (Γ : gmap string (sem_ty Σ)) (e : expr) (A : sem_ty Σ) : iProp Σ :=
  tc_opaque (□ ∀ vs, env_sem_typed Γ vs -∗ WP subst_map vs e {{ A }})%I.
Instance: Params (@sem_typed) 2 := {}.
Notation "Γ ⊨ e : A" := (sem_typed Γ e A)
  (at level 100, e at next level, A at level 200).

Section sem_typed.
  Context `{heapG Σ}.
  Implicit Types A B : sem_ty Σ.
  Implicit Types C : sem_ty Σ → sem_ty Σ.

  Global Instance env_sem_typed_ne n :
    Proper (dist n ==> (=) ==> dist n) (@env_sem_typed Σ _).
  Proof. Admitted.
  Global Instance env_sem_typed_proper :
    Proper ((≡) ==> (=) ==> (≡)) (@env_sem_typed Σ _).
  Proof. intros ??????. subst. rewrite /env_sem_typed. Admitted.
  Global Instance sem_typed_ne n :
    Proper (dist n ==> (=) ==> dist n ==> dist n) (@sem_typed Σ _).
  Proof. solve_proper. Qed.
  Global Instance sem_typed_proper :
    Proper ((≡) ==> (=) ==> (≡) ==> (≡)) (@sem_typed Σ _).
  Proof. solve_proper. Qed.

  Global Instance sem_typed_persistent Γ e A : Persistent (Γ ⊨ e : A).
  Proof. rewrite /sem_typed /=. apply _. Qed.

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

  Lemma env_sem_typed_empty vs : env_sem_typed ∅ vs -∗ ⌜vs = ∅⌝.
  Proof. by iIntros "?"; iApply big_sepM2_empty_r. Qed.
End sem_typed.
