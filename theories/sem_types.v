From tutorial_popl20 Require Export base.
From iris.heap_lang Require Export proofmode.
From iris.base_logic.lib Require Export invariants.

(* The domain of semantic types: persistent Iris predicates over values *)
Record sem_ty Σ := SemTy {
  sem_ty_car :> val → iProp Σ;
  sem_ty_persistent v : Persistent (sem_ty_car v)
}.
Arguments SemTy {_} _%I {_}.
Arguments sem_ty_car {_} _ _ : simpl never.
Bind Scope sem_ty_scope with sem_ty.
Delimit Scope sem_ty_scope with sem_ty.
Existing Instance sem_ty_persistent.

(* The COFE structure on semantic types *)
Section sem_ty_cofe.
  Context `{Σ : gFunctors}.

  Instance sem_ty_equiv : Equiv (sem_ty Σ) := λ A B, ∀ w, A w ≡ B w.
  Instance sem_ty_dist : Dist (sem_ty Σ) := λ n A B, ∀ w, A w ≡{n}≡ B w.
  Lemma sem_ty_ofe_mixin : OfeMixin (sem_ty Σ).
  Proof. by apply (iso_ofe_mixin (sem_ty_car : _ → val -d> _)). Qed.
  Canonical Structure sem_tyO := OfeT (sem_ty Σ) sem_ty_ofe_mixin.
  Global Instance sem_ty_cofe : Cofe sem_tyO.
  Proof.
    apply (iso_cofe_subtype' (λ A : val -d> iPropO Σ, ∀ w, Persistent (A w))
      (@SemTy _) sem_ty_car)=> //.
    - apply _.
    - apply limit_preserving_forall=> w.
      by apply bi.limit_preserving_Persistent=> n ??.
  Qed.

  Global Instance sem_ty_inhabited : Inhabited (sem_ty Σ) := populate (SemTy inhabitant).

  Global Instance sem_ty_car_ne n : Proper (dist n ==> (=) ==> dist n) sem_ty_car.
  Proof. by intros A A' ? w ? <-. Qed.
  Global Instance sem_ty_car_proper : Proper ((≡) ==> (=) ==> (≡)) sem_ty_car.
  Proof. by intros A A' ? w ? <-. Qed.
End sem_ty_cofe.

Arguments sem_tyO : clear implicits.

(* The type formers *)
Section types.
  Context `{heapG Σ}.

  Definition sem_ty_unit : sem_ty Σ := SemTy (λ w, ⌜ w = #() ⌝)%I.
  Definition sem_ty_bool : sem_ty Σ := SemTy (λ w, ∃ b : bool, ⌜ w = #b ⌝)%I.
  Definition sem_ty_int : sem_ty Σ := SemTy (λ w, ∃ n : Z, ⌜ w = #n ⌝)%I.

  Definition sem_ty_arr (A1 A2 : sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    □ ∀ v, A1 v -∗ WP App w v {{ A2 }})%I.

  Definition sem_ty_prod (A1 A2 : sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    ∃ w1 w2, ⌜w = PairV w1 w2⌝ ∧ A1 w1 ∧ A2 w2)%I.
  Definition sem_ty_sum (A1 A2 : sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    (∃ w1, ⌜w = InjLV w1⌝ ∧ A1 w1) ∨ (∃ w2, ⌜w = InjRV w2⌝ ∧ A2 w2))%I.

  Definition sem_ty_forall (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    □ ∀ A : sem_ty Σ, WP w #() {{ w, C A w }})%I.
  Definition sem_ty_exist (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    ∃ A : sem_ty Σ, C A w)%I.

  Definition tyN := nroot .@ "ty".
  Definition sem_ty_ref (A : sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    ∃ l : loc, ⌜w = #l⌝ ∧ inv (tyN .@ l) (∃ v, l ↦ v ∗ A v))%I.
End types.

Instance: Params (@sem_ty_arr) 1 := {}.
Instance: Params (@sem_ty_prod) 1 := {}.
Instance: Params (@sem_ty_sum) 1 := {}.
Instance: Params (@sem_ty_forall) 1 := {}.
Instance: Params (@sem_ty_exist) 1 := {}.
Instance: Params (@sem_ty_ref) 2 := {}.

(* Nice notations *)
Notation "()" := sem_ty_unit : sem_ty_scope.
Infix "→" := sem_ty_arr : sem_ty_scope.
Infix "*" := sem_ty_prod : sem_ty_scope.
Infix "+" := sem_ty_sum : sem_ty_scope.
Notation "∀ A1 .. An , C" :=
  (sem_ty_forall (λ A1, .. (sem_ty_forall (λ An, C%sem_ty)) ..)) : sem_ty_scope.
Notation "∃ A1 .. An , C" :=
  (sem_ty_exist (λ A1, .. (sem_ty_exist (λ An, C%sem_ty)) ..)) : sem_ty_scope.
Notation "'ref' A" := (sem_ty_ref A) : sem_ty_scope.

Section types_properties.
  Context `{heapG Σ}.

  (* All type formers are non-expansive *)
  Global Instance sem_ty_prod_ne : NonExpansive2 (@sem_ty_prod Σ).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_sum_ne : NonExpansive2 (@sem_ty_sum Σ).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_arr_ne : NonExpansive2 (@sem_ty_arr Σ _).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_forall_ne n : Proper (pointwise_relation _ (dist n) ==> dist n) (@sem_ty_forall Σ _).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_exist_ne n : Proper (pointwise_relation _ (dist n) ==> dist n) (@sem_ty_exist Σ).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_ref_ne : NonExpansive2 (@sem_ty_ref Σ _).
  Proof. solve_proper. Qed.

  (* All type formers respect setoid equality *)
  Global Instance sem_ty_prod_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sem_ty_prod Σ).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_sum_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sem_ty_sum Σ).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_arr_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sem_ty_arr Σ _).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_forall_proper : Proper (pointwise_relation _ (≡) ==> (≡)) (@sem_ty_forall Σ _).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_exist_proper : Proper (pointwise_relation _ (≡) ==>(≡)) (@sem_ty_exist Σ).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_ref_proper : Proper ((≡) ==> (≡)) (@sem_ty_ref Σ _).
  Proof. solve_proper. Qed.
End types_properties.
