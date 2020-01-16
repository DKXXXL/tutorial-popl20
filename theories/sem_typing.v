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

  (* The semantic typing rules *)
  Lemma sem_typed_var Γ (x : string) A : Γ !! x = Some A → Γ ⊨ x : A.
  Proof.
    iIntros (HΓx vs) "!# #HΓ /=".
    iDestruct (env_sem_typed_lookup with "HΓ") as (v ->) "HA"; first done.
    by iApply wp_value.
  Qed.

  Lemma sem_typed_unit Γ : Γ ⊨ #() : ().
  Proof. iIntros (vs) "!# _ /=". by iApply wp_value. Qed.
  Lemma sem_typed_bool Γ (b : bool) : Γ ⊨ #b : sem_ty_bool.
  Proof. iIntros (vs) "!# _ /=". iApply wp_value. rewrite /sem_ty_car /=. eauto. Qed.
  Lemma sem_typed_int Γ (n : Z) : Γ ⊨ #n : sem_ty_int.
  Proof. iIntros (vs) "!# _ /=". iApply wp_value. rewrite /sem_ty_car /=. eauto. Qed.

  Lemma sem_typed_pair Γ e1 e2 A1 A2 :
    (Γ ⊨ e1 : A1) -∗ (Γ ⊨ e2 : A2) -∗ Γ ⊨ (e1,e2) : A1 * A2.
  Proof.
    iIntros "#H1 #H2" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H2 [//])"); iIntros (w2) "#HA2".
    wp_apply (wp_wand with "(H1 [//])"); iIntros (w1) "#HA1".
    wp_pures. iExists w1, w2. auto.
  Qed.
  Lemma sem_typed_fst Γ e A1 A2 : (Γ ⊨ e : A1 * A2) -∗ Γ ⊨ Fst e : A1.
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H [//])"); iIntros (w).
    iDestruct 1 as (w1 w2 ->) "[??]". by wp_pures.
  Qed.
  Lemma sem_typed_snd Γ e A1 A2 : (Γ ⊨ e : A1 * A2) -∗ Γ ⊨ Snd e : A2.
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H [//])"); iIntros (w).
    iDestruct 1 as (w1 w2 ->) "[??]". by wp_pures.
  Qed.

  Lemma sem_typed_injl Γ e A1 A2 : (Γ ⊨ e : A1) -∗ Γ ⊨ InjL e : A1 + A2.
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H [//])"); iIntros (w) "#HA".
    wp_pures. iLeft. iExists w. auto.
  Qed.
  Lemma sem_typed_injr Γ e A1 A2 : (Γ ⊨ e : A2) -∗ Γ ⊨ InjR e : A1 + A2.
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H [//])"); iIntros (w) "#HA".
    wp_pures. iRight. iExists w. auto.
  Qed.
  Lemma sem_typed_case Γ e e1 e2 A1 A2 B :
    (Γ ⊨ e : A1 + A2) -∗ (Γ ⊨ e1 : A1 → B) -∗ (Γ ⊨ e2 : A2 → B) -∗
    Γ ⊨ Case e e1 e2 : B.
  Proof.
    iIntros "#H #H1 #H2" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H [//])"); iIntros (w) "#[HA|HA]".
    - iDestruct "HA" as (w1 ->) "HA". wp_pures.
      wp_apply (wp_wand with "(H1 [//])"); iIntros (v) "#HAB". by iApply "HAB".
    - iDestruct "HA" as (w2 ->) "HA". wp_pures.
      wp_apply (wp_wand with "(H2 [//])"); iIntros (v) "#HAB". by iApply "HAB".
  Qed.

  Lemma sem_typed_rec Γ f x e A1 A2 :
    (binder_insert f (A1 → A2)%sem_ty (binder_insert x A1 Γ) ⊨ e : A2) -∗
    Γ ⊨ (rec: f x := e) : A1 → A2.
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=". wp_pures. iLöb as "IH".
    iIntros "!#" (v) "#HA1". wp_pures. set (r := RecV f x _).
    iSpecialize ("H" $! (binder_insert f r (binder_insert x v vs)) with "[#]").
    { iApply (env_sem_typed_insert with "IH"). by iApply env_sem_typed_insert. }
    destruct x as [|x], f as [|f]; rewrite /= -?subst_map_insert //.
    destruct (decide (x = f)) as [->|].
    - by rewrite subst_subst delete_idemp insert_insert -subst_map_insert.
    - rewrite subst_subst_ne // -subst_map_insert.
      by rewrite -delete_insert_ne // -subst_map_insert.
  Qed.

  Lemma sem_typed_app Γ e1 e2 A1 A2 :
    (Γ ⊨ e1 : A1 → A2) -∗ (Γ ⊨ e2 : A1) -∗ Γ ⊨ e1 e2 : A2.
  Proof.
    iIntros "#H1 #H2" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H2 [//])"); iIntros (w) "#HA1".
    wp_apply (wp_wand with "(H1 [//])"); iIntros (v) "#HA". by iApply "HA".
  Qed.

  Lemma sem_typed_tlam Γ e C : (∀ A, Γ ⊨ e : C A) -∗ Γ ⊨ (Λ: e) : ∀ A, C A.
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=". wp_pures.
    iIntros "!#" (A) "/=". wp_pures. by iApply ("H" $! A).
  Qed.
  Lemma sem_typed_tapp Γ e C A : (Γ ⊨ e : ∀ A, C A) -∗ Γ ⊨ e ! : C A.
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H [//])"); iIntros (w) "#HB". by iApply ("HB" $! A).
  Qed.

  Lemma sem_typed_pack Γ e C A : (Γ ⊨ e : C A) -∗ Γ ⊨ e : ∃ A, C A.
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H [//])"); iIntros (w) "#HB". by iExists A.
  Qed.
  Lemma sem_typed_unpack Γ x e1 e2 C B :
    (Γ ⊨ e1 : ∃ A, C A) -∗ (∀ A, binder_insert x (C A) Γ ⊨ e2 : B) -∗
    Γ ⊨ (unpack: x := e1 in e2) : B.
  Proof.
    iIntros "#H1 #H2" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H1 [//])"); iIntros (v); iDestruct 1 as (A) "#HC".
    rewrite /exist_unpack; wp_pures. rewrite -subst_map_binder_insert.
    wp_apply (wp_wand with "(H2 [])").
    { by iApply env_sem_typed_insert. }
    auto.
  Qed.

  Lemma sem_typed_alloc Γ e A : (Γ ⊨ e : A) -∗ Γ ⊨ ref e : ref A.
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_bind (subst_map _ e). iApply (wp_wand with "(H [//])"); iIntros (w) "HA".
    iApply wp_fupd. wp_alloc l as "Hl".
    iMod (inv_alloc (tyN .@ l) _ (∃ v, l ↦ v ∗ A v)%I with "[Hl HA]") as "#?".
    { iExists w. iFrame. }
    iModIntro. iExists l; auto.
  Qed.
  Lemma sem_typed_load Γ e A : (Γ ⊨ e : ref A) -∗ Γ ⊨ ! e : A.
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_bind (subst_map _ e). iApply (wp_wand with "(H [//])"); iIntros (w).
    iDestruct 1 as (l ->) "#?".
    iInv (tyN.@l) as (v) "[>Hl HA]". wp_load. eauto 10.
  Qed.
  Lemma sem_typed_store Γ e1 e2 A :
    (Γ ⊨ e1 : ref A) -∗ (Γ ⊨ e2 : A) -∗ Γ ⊨ (e1 <- e2) : ().
  Proof.
    iIntros "#H1 #H2" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H2 [//])"); iIntros (w2) "#HA".
    wp_apply (wp_wand with "(H1 [//])"); iIntros (w1); iDestruct 1 as (l ->) "#?".
    iInv (tyN.@l) as (v) "[>Hl _]". wp_store. eauto 10.
  Qed.
  Lemma sem_typed_faa Γ e1 e2 :
    (Γ ⊨ e1 : ref sem_ty_int) -∗ (Γ ⊨ e2 : sem_ty_int) -∗ Γ ⊨ FAA e1 e2 : sem_ty_int.
  Proof.
    iIntros "#H1 #H2" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H2 [//])"); iIntros (w2); iDestruct 1 as (n) "->".
    wp_apply (wp_wand with "(H1 [//])"); iIntros (w1); iDestruct 1 as (l ->) "#?".
    iInv (tyN.@l) as (v) "[>Hl Hv]"; iDestruct "Hv" as (n') "> ->".
    wp_faa. iModIntro. eauto 10.
  Qed.
  Lemma sem_typed_cmpxchg Γ A e1 e2 e3 :
    SemTyUnboxed A →
    (Γ ⊨ e1 : ref A) -∗ (Γ ⊨ e2 : A) -∗ (Γ ⊨ e3 : A) -∗ Γ ⊨ CmpXchg e1 e2 e3 : A * sem_ty_bool.
  Proof.
    intros. iIntros "#H1 #H2 #H3" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H3 [//])"); iIntros (w3) "HA3".
    wp_apply (wp_wand with "(H2 [//])"); iIntros (w2) "HA2".
    iDestruct (sem_ty_unboxed with "HA2") as %?.
    wp_apply (wp_wand with "(H1 [//])"); iIntros (w1); iDestruct 1 as (l ->) "#?".
    iInv (tyN.@l) as (v) "[>Hl #Hv]". wp_cmpxchg as ?|?; iModIntro;
      (iSplitL; [by eauto 12 with iFrame | iExists _, _; eauto]).
  Qed.

  Lemma sem_typed_un_op Γ e op A B :
    SemTyUnOp op A B → (Γ ⊨ e : A) -∗ Γ ⊨ UnOp op e : B.
  Proof.
    intros ?. iIntros "#H" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H [//])"); iIntros (v) "#HA".
    iDestruct (sem_ty_un_op with "HA") as (w ?) "#HB". by wp_unop.
  Qed.
  Lemma sem_typed_bin_op Γ e1 e2 op A1 A2 B :
    SemTyBinOp op A1 A2 B → (Γ ⊨ e1 : A1) -∗ (Γ ⊨ e2 : A2) -∗ Γ ⊨ BinOp op e1 e2 : B.
  Proof.
    intros. iIntros "#H1 #H2" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H2 [//])"); iIntros (v2) "#HA2".
    wp_apply (wp_wand with "(H1 [//])"); iIntros (v1) "#HA1".
    iDestruct (sem_ty_bin_op with "HA1 HA2") as (w ?) "#HB". by wp_binop.
  Qed.

  Lemma sem_typed_if Γ e e1 e2 B :
    (Γ ⊨ e : sem_ty_bool) -∗ (Γ ⊨ e1 : B) -∗ (Γ ⊨ e2 : B) -∗
    Γ ⊨ (if: e then e1 else e2) : B.
  Proof.
    iIntros "#H #H1 #H2" (vs) "!# #HΓ /=".
    iSpecialize ("H1" with "HΓ"). iSpecialize ("H2" with "HΓ").
    wp_apply (wp_wand with "(H [//])"); iIntros (w). iDestruct 1 as ([]) "->"; by wp_if.
  Qed.

  Lemma sem_typed_fork Γ e : (Γ ⊨ e : ()) -∗ Γ ⊨ Fork e : ().
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_apply wp_fork; last done. by iApply (wp_wand with "(H [//])").
  Qed.
End typed_properties.
