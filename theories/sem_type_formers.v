From tutorial_popl20 Require Export sem_types.

(** The definitions of the type formers *)
Section types.
  Context `{heapG Σ}.

  (** Let us start with the simplest types of our language: unit and Boolean.
  The value interpretations of these types are as follows: *)
  Definition sem_ty_unit : sem_ty Σ := SemTy (λ w, ⌜ w = #() ⌝)%I.
  Definition sem_ty_bool : sem_ty Σ := SemTy (λ w, ∃ b : bool, ⌜ w = #b ⌝)%I.
  (** These interpretations are exactly what you would expect: the only value
  of the unit type is the unit value [()], the values of the Boolean type are
  the elements of the Coq type [bool] (i.e. [true] and [false]). *)

  (** Exercise. now define the value interpretation of the integer type. *)
  (* REMOVE *) Definition sem_ty_int : sem_ty Σ := SemTy (λ w, ∃ n : Z, ⌜ w = #n ⌝)%I.

  (** The value interpretation for product type is as one would expect: *)
  Definition sem_ty_prod (A1 A2 : sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    ∃ w1 w2, ⌜w = PairV w1 w2⌝ ∧ A1 w1 ∧ A2 w2)%I.
  (** Values of the product type over [A1] and [A2] should be tuples [(w1, w2)],
  where [w1] and [w2] should be in the interpretation of [A1] and [A2],
  respectively. *)

  (* REMOVE *) Definition sem_ty_sum (A1 A2 : sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    (∃ w1, ⌜w = InjLV w1⌝ ∧ A1 w1) ∨ (∃ w2, ⌜w = InjRV w2⌝ ∧ A2 w2))%I.

  Definition sem_ty_arr (A1 A2 : sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    □ ∀ v, A1 v -∗ WP App w v {{ A2 }})%I.

  Definition sem_ty_forall (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    □ ∀ A : sem_ty Σ, WP w #() {{ w, C A w }})%I.
  Definition sem_ty_exist (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    ∃ A : sem_ty Σ, C A w)%I.

  Definition tyN := nroot .@ "ty".
  Definition sem_ty_ref (A : sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    ∃ l : loc, ⌜w = #l⌝ ∧ inv (tyN .@ l) (∃ v, l ↦ v ∗ A v))%I.
End types.

(** We introduce nicely looking notations for our semantic types. This allows
us to write lemmas, for example, the compatibility lemmas, in a readable way. *)
Notation "()" := sem_ty_unit : sem_ty_scope.
Infix "*" := sem_ty_prod : sem_ty_scope.
Infix "+" := sem_ty_sum : sem_ty_scope.
Infix "→" := sem_ty_arr : sem_ty_scope.
Notation "∀ A1 .. An , C" :=
  (sem_ty_forall (λ A1, .. (sem_ty_forall (λ An, C%sem_ty)) ..)) : sem_ty_scope.
Notation "∃ A1 .. An , C" :=
  (sem_ty_exist (λ A1, .. (sem_ty_exist (λ An, C%sem_ty)) ..)) : sem_ty_scope.
Notation "'ref' A" := (sem_ty_ref A) : sem_ty_scope.

(** A [Params t n] instance tells Coq's setoid rewriting mechanism _not_ to
rewrite in the first [n] arguments of [t]. These instances tend to make the
setoid rewriting mechanism a lot faster. This code is mostly boilerplate. *)
Instance: Params (@sem_ty_arr) 1 := {}.
Instance: Params (@sem_ty_prod) 1 := {}.
Instance: Params (@sem_ty_sum) 1 := {}.
Instance: Params (@sem_ty_forall) 1 := {}.
Instance: Params (@sem_ty_exist) 1 := {}.
Instance: Params (@sem_ty_ref) 2 := {}.

(** We prove that all type formers are non-expansive and respect setoid
equality. This code is mostly boilerplate. *)
Section types_properties.
  Context `{heapG Σ}.

  Global Instance sem_ty_prod_ne : NonExpansive2 (@sem_ty_prod Σ).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_sum_ne : NonExpansive2 (@sem_ty_sum Σ).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_arr_ne : NonExpansive2 (@sem_ty_arr Σ _).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_forall_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@sem_ty_forall Σ _).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_exist_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@sem_ty_exist Σ).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_ref_ne : NonExpansive2 (@sem_ty_ref Σ _).
  Proof. solve_proper. Qed.

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
