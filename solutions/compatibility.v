From tutorial_popl20 Require Export sem_typed sem_operators.

(** * Compatibility lemmas *)
(** We prove that the logical relations, i.e., the semantic typing judgment,
that we have defined is compatible with typing rules. That is, the logical
relations is a congruence with respect to the typing rules.

These compatibility lemmas are what one gets when the syntactic typing judgment
is replaced semantic typing judgment in syntactic typing rules. For instance
([sem_typed_pair]):

<<
   Γ ⊢ e1 : τ1        Γ ⊢ e2 : τ2
  --------------------------------
       Γ ⊢ (e1, e2) : τ1 × τ2
>>

becomes:

<<
  (Γ ⊨ e1 : A1) -∗ (Γ ⊨ e2 : A2) -∗ Γ ⊢ (e1, e2) : A1 * A2
>>
*)

Section compatibility.
  Context `{!heapG Σ}.
  Implicit Types A B : sem_ty Σ.
  Implicit Types C : sem_ty Σ → sem_ty Σ.

  (** * Compatibility rules for expression typing *)
  (** * Variables *)
  Lemma Var_sem_typed Γ (x : string) A : Γ !! x = Some A → (Γ ⊨ x : A)%I.
  Proof.
    iIntros (HΓx vs) "!# #HΓ /=".
    iDestruct (env_sem_typed_lookup with "HΓ") as (v ->) "HA"; first done.
    by iApply wp_value.
  Qed.

  Lemma Val_sem_typed Γ v A : ⊨ᵥ v : A -∗ Γ ⊨ v : A.
  Proof.
    iIntros "#Hv" (vs) "!# #HΓ /=".
    iApply wp_value. iApply "Hv".
  Qed.

  (** * Products and sums *)
  Lemma Pair_sem_typed Γ e1 e2 A1 A2 :
    Γ ⊨ e1 : A1 -∗ Γ ⊨ e2 : A2 -∗ Γ ⊨ (e1,e2) : A1 * A2.
  Proof.
    iIntros "#H1 #H2" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H2 [//])"); iIntros (w2) "#HA2".
    wp_apply (wp_wand with "(H1 [//])"); iIntros (w1) "#HA1".
    wp_pures. iExists w1, w2. auto.
  Qed.
  Lemma Fst_sem_typed Γ e A1 A2 : Γ ⊨ e : A1 * A2 -∗ Γ ⊨ Fst e : A1.
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H [//])"); iIntros (w).
    iDestruct 1 as (w1 w2 ->) "[??]". by wp_pures.
  Qed.
  (* REMOVE *) Lemma Snd_sem_typed Γ e A1 A2 : Γ ⊨ e : A1 * A2 -∗ Γ ⊨ Snd e : A2.
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H [//])"); iIntros (w).
    iDestruct 1 as (w1 w2 ->) "[??]". by wp_pures.
  Qed.

  Lemma InjL_sem_typed Γ e A1 A2 : Γ ⊨ e : A1 -∗ Γ ⊨ InjL e : A1 + A2.
  (* REMOVE *) Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H [//])"); iIntros (w) "#HA".
    wp_pures. iLeft. iExists w. auto.
  Qed.
  (* REMOVE *) Lemma InjR_sem_typed Γ e A1 A2 : Γ ⊨ e : A2 -∗ Γ ⊨ InjR e : A1 + A2.
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H [//])"); iIntros (w) "#HA".
    wp_pures. iRight. iExists w. auto.
  Qed.
  Lemma Case_sem_typed Γ e e1 e2 A1 A2 B :
    Γ ⊨ e : A1 + A2 -∗ Γ ⊨ e1 : (A1 → B) -∗ Γ ⊨ e2 : (A2 → B) -∗
    Γ ⊨ Case e e1 e2 : B.
  (* REMOVE *) Proof.
    iIntros "#H #H1 #H2" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H [//])"); iIntros (w) "#[HA|HA]".
    - iDestruct "HA" as (w1 ->) "HA". wp_pures.
      wp_apply (wp_wand with "(H1 [//])"); iIntros (v) "#HAB". by iApply "HAB".
    - iDestruct "HA" as (w2 ->) "HA". wp_pures.
      wp_apply (wp_wand with "(H2 [//])"); iIntros (v) "#HAB". by iApply "HAB".
  Qed.

  (** * Functions *)
  Lemma Rec_sem_typed Γ f x e A1 A2 :
    binder_insert f (A1 → A2)%sem_ty (binder_insert x A1 Γ) ⊨ e : A2 -∗
    Γ ⊨ (rec: f x := e) : (A1 → A2).
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=". wp_pures. iLöb as "IH".
    iIntros "!#" (v) "#HA1". wp_pures. set (r := RecV f x _).
    rewrite -subst_map_binder_insert_2. iApply "H".
    iApply (env_sem_typed_insert with "IH"). by iApply env_sem_typed_insert.
  Qed.

  Lemma App_sem_typed Γ e1 e2 A1 A2 :
    Γ ⊨ e1 : (A1 → A2) -∗ Γ ⊨ e2 : A1 -∗ Γ ⊨ e1 e2 : A2.
  Proof.
    iIntros "#H1 #H2" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H2 [//])"); iIntros (w) "#HA1".
    wp_apply (wp_wand with "(H1 [//])"); iIntros (v) "#HA". by iApply "HA".
  Qed.

  (** * Polymorphic functions and existentials *)
  Lemma TLam_sem_typed Γ e C : (∀ A, Γ ⊨ e : C A) -∗ Γ ⊨ (Λ: e) : ∀ A, C A.
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=". wp_pures.
    iIntros "!#" (A) "/=". wp_pures. by iApply ("H" $! A).
  Qed.
  Lemma TApp_sem_typed Γ e C A : (Γ ⊨ e : ∀ A, C A) -∗ Γ ⊨ e <_> : C A.
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H [//])"); iIntros (w) "#HB". by iApply ("HB" $! A).
  Qed.

  Lemma Pack_sem_typed Γ e C A : Γ ⊨ e : C A -∗ Γ ⊨ (pack: e) : ∃ A, C A.
  (* REMOVE *) Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H [//])"); iIntros (w) "#HB".
    wp_lam. by iExists A.
  Qed.
  Lemma Unpack_sem_typed Γ x e1 e2 C B :
    (Γ ⊨ e1 : ∃ A, C A) -∗ (∀ A, binder_insert x (C A) Γ ⊨ e2 : B) -∗
    Γ ⊨ (unpack: x := e1 in e2) : B.
  (* REMOVE *) Proof.
    iIntros "#H1 #H2" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H1 [//])"); iIntros (v); iDestruct 1 as (A) "#HC".
    rewrite /exist_unpack; wp_pures. rewrite -subst_map_binder_insert.
    wp_apply (wp_wand with "(H2 [])").
    { by iApply env_sem_typed_insert. }
    auto.
  Qed.

  (** ** Heap operations *)
  Lemma Alloc_sem_typed Γ e A : Γ ⊨ e : A -∗ Γ ⊨ ref e : ref A.
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_bind (subst_map _ e). iApply (wp_wand with "(H [//])"); iIntros (w) "HA".
    iApply wp_fupd. wp_alloc l as "Hl".
    iMod (inv_alloc (tyN .@ l) _ (∃ v, l ↦ v ∗ A v)%I with "[Hl HA]") as "#?".
    { iExists w. iFrame. }
    iModIntro. iExists l; auto.
  Qed.
  Lemma Load_sem_typed Γ e A : Γ ⊨ e : ref A -∗ Γ ⊨ ! e : A.
  Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_bind (subst_map _ e). iApply (wp_wand with "(H [//])"); iIntros (w).
    iDestruct 1 as (l ->) "#?".
    iInv (tyN.@l) as (v) "[>Hl HA]". wp_load. eauto 10.
  Qed.
  Lemma Store_sem_typed Γ e1 e2 A :
    Γ ⊨ e1 : ref A -∗ Γ ⊨ e2 : A -∗ Γ ⊨ (e1 <- e2) : ().
  (* REMOVE *) Proof.
    iIntros "#H1 #H2" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H2 [//])"); iIntros (w2) "#HA".
    wp_apply (wp_wand with "(H1 [//])"); iIntros (w1); iDestruct 1 as (l ->) "#?".
    iInv (tyN.@l) as (v) "[>Hl _]". wp_store. eauto 10.
  Qed.
  Lemma FAA_sem_typed Γ e1 e2 :
    Γ ⊨ e1 : ref sem_ty_int -∗ Γ ⊨ e2 : sem_ty_int -∗ Γ ⊨ FAA e1 e2 : sem_ty_int.
  (* REMOVE *) Proof.
    iIntros "#H1 #H2" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H2 [//])"); iIntros (w2); iDestruct 1 as (n) "->".
    wp_apply (wp_wand with "(H1 [//])"); iIntros (w1); iDestruct 1 as (l ->) "#?".
    iInv (tyN.@l) as (v) "[>Hl Hv]"; iDestruct "Hv" as (n') "> ->".
    wp_faa. iModIntro. eauto 10.
  Qed.
  Lemma CmpXchg_sem_typed Γ A e1 e2 e3 :
    SemTyUnboxed A →
    Γ ⊨ e1 : ref A -∗ Γ ⊨ e2 : A -∗ Γ ⊨ e3 : A -∗
    Γ ⊨ CmpXchg e1 e2 e3 : A * sem_ty_bool.
  (* REMOVE *) Proof.
    intros. iIntros "#H1 #H2 #H3" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H3 [//])"); iIntros (w3) "HA3".
    wp_apply (wp_wand with "(H2 [//])"); iIntros (w2) "HA2".
    iDestruct (sem_ty_unboxed with "HA2") as %?.
    wp_apply (wp_wand with "(H1 [//])"); iIntros (w1); iDestruct 1 as (l ->) "#?".
    iInv (tyN.@l) as (v) "[>Hl #Hv]". wp_cmpxchg as ?|?; iModIntro;
      (iSplitL; [by eauto 12 with iFrame | iExists _, _; eauto]).
  Qed.

  (** ** Operators *)
  Lemma UnOp_sem_typed Γ e op A B :
    SemTyUnOp op A B → Γ ⊨ e : A -∗ Γ ⊨ UnOp op e : B.
  Proof.
    intros ?. iIntros "#H" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H [//])"); iIntros (v) "#HA".
    iDestruct (sem_ty_un_op with "HA") as (w ?) "#HB". by wp_unop.
  Qed.
  Lemma BinOp_sem_typed Γ e1 e2 op A1 A2 B :
    SemTyBinOp op A1 A2 B → Γ ⊨ e1 : A1 -∗ Γ ⊨ e2 : A2 -∗ Γ ⊨ BinOp op e1 e2 : B.
  (* REMOVE *) Proof.
    intros. iIntros "#H1 #H2" (vs) "!# #HΓ /=".
    wp_apply (wp_wand with "(H2 [//])"); iIntros (v2) "#HA2".
    wp_apply (wp_wand with "(H1 [//])"); iIntros (v1) "#HA1".
    iDestruct (sem_ty_bin_op with "HA1 HA2") as (w ?) "#HB". by wp_binop.
  Qed.

  Lemma If_sem_typed Γ e e1 e2 B :
    Γ ⊨ e : sem_ty_bool -∗ Γ ⊨ e1 : B -∗ Γ ⊨ e2 : B -∗
    Γ ⊨ (if: e then e1 else e2) : B.
  (* REMOVE *) Proof.
    iIntros "#H #H1 #H2" (vs) "!# #HΓ /=".
    iSpecialize ("H1" with "HΓ"). iSpecialize ("H2" with "HΓ").
    wp_apply (wp_wand with "(H [//])"); iIntros (w). iDestruct 1 as ([]) "->"; by wp_if.
  Qed.

  (** ** Fork *)
  Lemma Fork_sem_typed Γ e : Γ ⊨ e : () -∗ Γ ⊨ Fork e : ().
  (* REMOVE *) Proof.
    iIntros "#H" (vs) "!# #HΓ /=".
    wp_apply wp_fork; last done. by iApply (wp_wand with "(H [//])").
  Qed.

  (** * Compatibility rules for value typing *)
  (** ** Base types *)
  Lemma UnitV_sem_typed : (⊨ᵥ #() : ())%I.
  Proof. by iPureIntro. Qed.
  Lemma BoolV_sem_typed (b : bool) : (⊨ᵥ #b : sem_ty_bool)%I.
  Proof. by iExists b. Qed.
  Lemma IntV_sem_typed (n : Z) : (⊨ᵥ #n : sem_ty_int)%I.
  (* REMOVE *) Proof. by iExists n. Qed.

  (** ** Products and sums *)
  Lemma PairV_sem_typed v1 v2 τ1 τ2 :
    ⊨ᵥ v1 : τ1 -∗ ⊨ᵥ v2 : τ2 -∗
    ⊨ᵥ PairV v1 v2 : (τ1 * τ2).
  Proof. iIntros "#H1 #H2". iExists v1, v2. auto. Qed.
  Lemma InjLV_sem_typed v τ1 τ2 :
    ⊨ᵥ v : τ1 -∗
    ⊨ᵥ InjLV v : (τ1 + τ2).
  Proof. iIntros "H". iLeft. auto. Qed.
  Lemma InjRV_sem_typed v τ1 τ2 :
    ⊨ᵥ v : τ2 -∗
    ⊨ᵥ InjRV v : (τ1 + τ2).
  Proof. iIntros "H". iRight. auto. Qed.

  (** ** Functions *)
  Lemma RecV_sem_typed f x e A B :
    binder_insert f (A → B)%sem_ty (binder_insert x A ∅) ⊨ e : B -∗
    ⊨ᵥ RecV f x e : (A → B).
  Proof.
    iIntros "#H". iLöb as "IH".
    iIntros "!#" (v) "#HA1". wp_pures. set (r := RecV f x _).
    rewrite -subst_map_binder_insert_2_empty. iApply "H".
    iApply (env_sem_typed_insert with "IH").
    iApply (env_sem_typed_insert with "[$]"). iApply env_sem_typed_empty.
  Qed.

  Lemma TLamV_sem_typed e C : (∀ A, ∅ ⊨ e : C A) -∗ ⊨ᵥ (Λ: e) : ∀ A, C A.
  Proof.
    iIntros "#H !#" (A) "/=". wp_pures.
    rewrite -{2}(subst_map_empty e). iApply ("H" $! A).
    by iApply env_sem_typed_empty.
  Qed.
End compatibility.
