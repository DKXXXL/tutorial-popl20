From tutorial_popl20 Require Export sem_types.

(** * The definitions of the semantic type formers

    These type formers correspond to those of syntactic types, e.g., a
    product former that given two semantic types [A] and [B], gives
    the semantic type of the product [A * B], i.e., values that are
    pairs where the first component belongs to [A] and the second
    component to [B]. *)
Section types.
  Context `{!heapG Σ}.

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
    ∃ w1 w2, ⌜w = (w1, w2)%V⌝ ∧ A1 w1 ∧ A2 w2)%I.
  (** Values of the product type over [A1] and [A2] should be tuples [(w1, w2)],
  where [w1] and [w2] should be in the interpretation of [A1] and [A2],
  respectively. *)

  (* REMOVE *) Definition sem_ty_sum (A1 A2 : sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    (∃ w1, ⌜w = InjLV w1⌝ ∧ A1 w1) ∨ (∃ w2, ⌜w = InjRV w2⌝ ∧ A2 w2))%I.

  (** The value interpretation for function types is as follows: *)
  Definition sem_ty_arr (A1 A2 : sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    □ ∀ v, A1 v -∗ WP App w v {{ A2 }})%I.
  (** This definition is very close to the usual way of defining the
      value interpretation of the function type [A1 → A2] in ordinary
      logical relations: it expresses that arguments of semantic type
      [A1] are mapped to results of semantic type [A2] . The only Iris
      specific feature one has to take into account is the [□]
      modality. Recall that the value interpretation should be a
      persistent predicate; however, even if both [P] and [Q] are
      persistent propositions, the magic wand [P -∗ Q] is not
      necessarily persistent. Hence, we use the [□] modality to make
      the magic wand persistent. *)



  (** The value interpretation for type variables, universal types,
      and existential types is: *)
  Definition sem_ty_forall (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    □ ∀ A : sem_ty Σ, WP w #() {{ w, C A w }})%I.
  Definition sem_ty_exist (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    ∃ A : sem_ty Σ, C A w)%I.
  (** The interpretations of these types are fairly straightforward.
      Given a higher-order type former [C] that maps semantic types to
      semantic types, we define the universal type [sem_ty_forall A]
      using the universal quantification in Iris. That is, a value [w]
      is considered a polymorphic value if for any semantic type [A],
      when [w] is specialized to the type [A] (written as [w #()] as
      (semantic) types never appear in terms in our untyped syntax)
      the _resulting expression_ is an expression in the semantics of
      the type [C A] (defined using WP).

      Similarly, given a higher-order type former [C] that maps
      semantic types to semantic types, we define the existential type
      [sem_ty_exist A] using the existential quantification in Iris.

      Notice how the impredicative nature of Iris propositions and
      predicates allows us to quantify over Iris predicates to define
      an Iris predicate. This is crucial for giving semantics to
      parametric polymorphism, i.e., universal and existential types.

      Remark: notice that for technical reasons (related to the value
      restriction problem in ML-like languages) universally quantified
      expressions are not evaluated until they are applied to a
      specific type. *)

  (** The value interpretation of reference types is as follows: *)
  Definition tyN := nroot .@ "ty".
  Definition sem_ty_ref (A : sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    ∃ l : loc, ⌜w = #l⌝ ∧ inv (tyN .@ l) (∃ v, l ↦ v ∗ A v))%I.
  (** Intuitively, values of the reference type [sem_ty_ref A] should
     be locations l that hold a value [w] in the semantic type [A] at
     all times. In order to express this intuition in a formal way, we
     make use of two features of Iris:

     - The points-to connective l ↦ v (from vanilla separation logic)
       provides exclusive ownership of the location l with value
       v. The points-to connective is an ephemeral proposition, and
       necessarily not a persistent proposition.

     - The invariant assertion [inv N P] expresses that a (typically
       ephemeral) proposition [P] holds at all times -- i.e., [P] is
       invariant. The invariant assertion is persistent. *)

  (** Remark: Iris is also capable giving semantics to recursive
   types. However, for the sake of simplicity we did not consider
   recursive types for this tutorial. In particular, to give the
   semantics of recursive types one needs to use Iris's guarded
   fixpoints, which require some additional bookkeeping related to
   contractiveness. *)
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
  Context `{!heapG Σ}.

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
