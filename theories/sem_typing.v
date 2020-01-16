From tutorial_popl20 Require Export sem_type_formers.

(* Typing for operators *)
Class SemTyUnboxed `{heapG Σ} (A : sem_ty Σ) :=
  sem_ty_unboxed v : A v -∗ ⌜ val_is_unboxed v ⌝.

Class SemTyUnOp `{heapG Σ} (op : un_op) (A B : sem_ty Σ) :=
  sem_ty_un_op v : A v -∗ ∃ w, ⌜ un_op_eval op v = Some w ⌝ ∧ B w.

Class SemTyBinOp `{heapG Σ} (op : bin_op) (A1 A2 B : sem_ty Σ) :=
  sem_ty_bin_op v1 v2 : A1 v1 -∗ A2 v2 -∗ ∃ w, ⌜ bin_op_eval op v1 v2 = Some w ⌝ ∧ B w.

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

Section typed_properties.
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

  (* Unboxed types *)
  Global Instance sem_ty_unit_unboxed : SemTyUnboxed ().
  Proof. by iIntros (v ->). Qed.
  Global Instance sem_ty_bool_unboxed : SemTyUnboxed sem_ty_bool.
  Proof. iIntros (v). by iDestruct 1 as (b) "->". Qed.
  Global Instance sem_ty_int_unboxed : SemTyUnboxed sem_ty_int.
  Proof. iIntros (v). by iDestruct 1 as (i) "->". Qed.
  Global Instance sem_ty_ref_unboxed A : SemTyUnboxed (ref A).
  Proof. iIntros (v). by iDestruct 1 as (i ->) "?". Qed.

  (* Operator typing *)
  Global Instance sem_ty_un_op_int op : SemTyUnOp op sem_ty_int sem_ty_int.
  Proof. iIntros (?). iDestruct 1 as (i) "->". destruct op; eauto. Qed.
  Global Instance sem_ty_un_op_bool : SemTyUnOp NegOp sem_ty_bool sem_ty_bool.
  Proof. iIntros (?). iDestruct 1 as (i) "->". eauto. Qed.

  Global Instance sem_ty_bin_op_eq A : SemTyUnboxed A → SemTyBinOp EqOp A A sem_ty_bool.
  Proof.
    iIntros (? v1 v2) "A1 _". rewrite /bin_op_eval /sem_ty_car /=.
    iDestruct (sem_ty_unboxed with "A1") as %Hunb.
    rewrite decide_True; last solve_vals_compare_safe.
    eauto.
  Qed.
  Global Instance sem_ty_bin_op_arith op :
    TCElemOf op [PlusOp; MinusOp; MultOp; QuotOp; RemOp;
                 AndOp; OrOp; XorOp; ShiftLOp; ShiftROp] →
    SemTyBinOp op sem_ty_int sem_ty_int sem_ty_int.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /sem_ty_car /=; eauto.
  Qed.
  Global Instance sem_ty_bin_op_compare op :
    TCElemOf op [LeOp; LtOp] →
    SemTyBinOp op sem_ty_int sem_ty_int sem_ty_bool.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /sem_ty_car /=; eauto.
  Qed.
  Global Instance sem_ty_bin_op_bool op :
    TCElemOf op [AndOp; OrOp; XorOp] →
    SemTyBinOp op sem_ty_bool sem_ty_bool sem_ty_bool.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /sem_ty_car /=; eauto.
  Qed.
End typed_properties.
