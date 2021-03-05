From exercises Require Export sem_types.

(** * Semantic type formers *)
(** For all of the type formers in the syntactic type system, we now define
corresponding semantic type formers. For example, we define the product type
formers, which given two semantic types [A] and [B], gives the semantic type of
the product [A * B], i.e., values that are pairs where the first component
belongs to [A] and the second component to [B]. *)

(** * Base types *)
(** Let us start with the simplest types of our language: unit, Boolean, and
integers. The corresponding semantic types are defined as follows: *)
Definition sem_ty_unit {Σ} : sem_ty Σ := SemTy (λ w,
  ⌜ w = #() ⌝)%I.
Definition sem_ty_bool {Σ} : sem_ty Σ := SemTy (λ w,
  ∃ b : bool, ⌜ w = #b ⌝)%I.
Definition sem_ty_int {Σ} : sem_ty Σ := SemTy (λ w,
  ∃ n : Z, ⌜ w = #n ⌝)%I.

(** These interpretations are exactly what you would expect: the only value
of the unit type is the unit value [()], the values of the Boolean type are
the elements of the Coq type [bool] (i.e. [true] and [false]), and the values
of the integer type are the integer literals. *)

(** * Products and sums *)
(** The semantic type former for products is as follows: *)
Definition sem_ty_prod {Σ} (A1 A2 : sem_ty Σ) : sem_ty Σ := SemTy (λ w,
  ∃ w1 w2, ⌜w = (w1, w2)%V⌝ ∧ A1 w1 ∧ A2 w2)%I.

(** Values of the product type over [A1] and [A2] should be tuples [(w1, w2)],
where [w1] and [w2] should values in the semantic type [A1] and [A2],
respectively. *)

(** The type former for sums is similar. *)
Definition sem_ty_sum {Σ} (A1 A2 : sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    (∃ w1, ⌜w = InjLV w1⌝ ∧ A1 w1)
  ∨ (∃ w2, ⌜w = InjRV w2⌝ ∧ A2 w2))%I.

(** * Functions *)
(** The semantic type former for functions is as follows: *)
Definition sem_ty_arr `{!heapG Σ} (A1 A2 : sem_ty Σ) : sem_ty Σ := SemTy (λ w,
  □ ∀ v, A1 v -∗ WP App w v {{ A2 }})%I.
(** This definition is very close to the usual way of defining the type
former for the function type [A1 → A2] in traditional logical relations: it
expresses that arguments of semantic type [A1] are mapped to results of
semantic type [A2]. The definition makes two of two features of Iris:

- The weakest precondition [WP e {{ Φ }}]. We have already seen weakest
  preconditions before (in the file [language.v]). We use them in the semantics
  of functions to talk about the result of the expression [v w].
- The persistence modality [□]. Recall that semantic types are persistent Iris
  predicates. However, even if both [P] and [Q] are persistent propositions,
  the magic wand [P -∗ Q] is not necessarily persistent. Hence, we use the [□
  modality to make the magic wand persistent.
*)

(** * Polymorphism and existentials *)
Definition sem_ty_forall `{!heapG Σ} (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := SemTy (λ w,
  □ ∀ A : sem_ty Σ, WP w <_> {{ w, C A w }})%I.
Definition sem_ty_exist {Σ} (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := SemTy (λ w,
  ∃ A : sem_ty Σ, C A w)%I.
(** The interpretations of these types are fairly straightforward. Given a
higher-order type former [C] that maps semantic types to semantic types, we
define the universal type [sem_ty_forall A] using the universal quantifier of
Iris. That is, a value [w] is considered a polymorphic value if for any semantic
type [A], when [w] is specialized to the type [A] (written as [w <_>] (see the
file [polymorphism.v]) as (semantic) types never appear in terms in our
untyped syntax) the _resulting expression_ is an expression in the semantics of
the type [C A] (defined using WP).

Similarly, given a higher-order type former [C] that maps semantic types to
semantic types, we define the existential type [sem_ty_exist A] using the
existential quantifier of Iris.

Notice how the impredicative nature of Iris propositions and predicates allow
us to quantify over Iris predicates to define an Iris predicate. This is crucial
for giving semantics to parametric polymorphism, i.e., universal and existential
types.

Remark: notice that for technical reasons (related to the value restriction
problem in ML-like languages) universally quantified expressions are not
evaluated until they are applied to a specific type. *)

(** * References *)
Definition tyN := nroot .@ "ty".
Definition sem_ty_ref `{!heapG Σ} (A : sem_ty Σ) : sem_ty Σ := SemTy (λ w,
  ∃ l : loc, ⌜w = #l⌝ ∧ inv (tyN .@ l) (∃ v, l ↦ v ∗ A v))%I.
(** Intuitively, values of the reference type [sem_ty_ref A] should be locations
[l] that hold a value [w] in the semantic type [A] at all times. In order to
express this intuition in a formal way, we make use of two features of Iris:

- The points-to connective [l ↦ v] (from vanilla separation logic) provides
  exclusive ownership of the location [l] with value [v]. The points-to
  connective is an ephemeral proposition, and necessarily not a persistent
  proposition.
- The invariant assertion [inv N P] expresses that a (typically ephemeral)
  proposition [P] holds at all times -- i.e., [P] is invariant. The invariant
  assertion is persistent.
*)

(** * Recursive types *)
Definition sem_ty_rec_pre {Σ} (C : sem_ty Σ → sem_ty Σ)
  (rec : sem_ty Σ) : sem_ty Σ := SemTy (λ v, ▷ ∃ rec', rec ≡ rec' ∧ C rec' v)%I.
Instance sem_ty_rec_pre_contractive {Σ} (C : sem_ty Σ → sem_ty Σ) :
  Contractive (sem_ty_rec_pre C).
Proof. solve_contractive. Qed.
Definition sem_ty_rec {Σ} (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ :=
  fixpoint (sem_ty_rec_pre C).

Lemma sem_ty_unfold {Σ} (C : sem_ty Σ → sem_ty Σ) `{!NonExpansive C} v :
  (sem_ty_rec C)%sem_ty v ⊣⊢ ▷ C (sem_ty_rec C)%sem_ty v.
Proof.
  rewrite {1}/sem_ty_rec (fixpoint_unfold (sem_ty_rec_pre C)) {1}/sem_ty_car /=.
  f_equiv. iSplit; [|by auto].
  iDestruct 1 as (rec') "[Hrec HC]". by iRewrite -"Hrec" in "HC".
Qed.
(** The recursive type [μ A, C A] is used to construct iso-recursive types. For
example, lists with elements of type [B] are defined as [μ A. ref (1 + (B ∗ A))],
where the left hand-side of the sum indicates the list is "nil" and the right
hand-side indicates the list is a "cons".

In the formal version in Coq, the recursive type is defined by [sem_ty_rec C]
where [C] is a function that describes the recursive structure. For lists with
elements of type [B], the function [C] is [λ A, ref (1 + (B ∗ A))].

We want to define [μ A, C A] in such a way that is a fixpoint of [C], i.e.,
[μ A, C A] should be isomorphic to [C (μ A, C A)]. Since [C] can be an arbitrary
function (there are no restrictions on the variance of the argument [A], or in
other words, it is not required to be functorial), such a fixpoint does not
exist.

To remedy that problem, we make use of Iris's ability to construct "guarded
fixpoints". Iris's guarded fixpoint operator [fixpoint (λ x, t)] can be used
to define recursive predicates without a restriction on the variance of the
recursive occurrences of [x] in [t]. In return for this flexibility, all
recursive occurrences of [x] must be guarded, meaning that they must appear
below a later modality ([▷])--i.e., within a term of the form [▷ P]. Subject to
this restriction, we obtain [fixpoint f = f (fixpoint f)].

Using Iris's guarded fixpoint operator, we define the type [sem_ty_rec C] as
[fixpoint (λ rec v, ▷ C (rec v))], which gives us that [sem_ty_rec] satisfies
the fixpoint equation [sem_ty_rec C ≡ ▷ C (sem_ty_rec C)].

The actual definition [sem_ty_rec] involves several auxiliary definitions to
convince Coq that [sem_ty_rec] is well defined. Concretely, [fixpoint f] is
well-defined only if [f] is [Contractive] (this is captured by the implicit
argument [Contractive f] of [fixpoint f]), which for the definition of
[sem_ty_rec C] means that [C] should non-expansive.

Since it is inconvenient to add an implicit argument to [sem_ty_rec] to require
that [C] is non-expansiveness, we make use of a trick. We define [sem_ty_rec C]
as [fixpoint f] with [f := λ rec v, ▷ ∃ rec', rec ≡ rec' ∧ C (rec' v)]. This
makes sure that [f] is contractive by construction, regardless of [C].

The unfolding lemma [sem_ty_unfold] establishes that [sem_ty_rec C] satisfies
the fixpoint equation, but only when [C] is be non-expansive. This means that
when defining types, we do not have to worry about non-expansiveness of [C],
but only when carrying out proofs, we need to prove non-expansiveness of [C].
Such non-expansiveness proofs can typically be automated using the tactic
[solve_proper].

Important: When carrying out proofs about recursive types in Coq, one should
never unfold the definition of [sem_ty_rec], but use the unfolding lemma
[sem_ty_unfold] instead. *)

(** * Notations *)
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
Notation "'μ' A , C" := (sem_ty_rec (λ A, C)) (at level 200) : sem_ty_scope.

(** A [Params t n] instance tells Coq's setoid rewriting mechanism *not* to
rewrite in the first [n] arguments of [t]. These instances tend to make the
setoid rewriting mechanism a lot faster. This code is mostly boilerplate. *)
Instance: Params (@sem_ty_prod) 1 := {}.
Instance: Params (@sem_ty_sum) 1 := {}.
Instance: Params (@sem_ty_arr) 1 := {}.
Instance: Params (@sem_ty_forall) 2 := {}.
Instance: Params (@sem_ty_exist) 1 := {}.
Instance: Params (@sem_ty_ref) 2 := {}.
Instance: Params (@sem_ty_rec) 1 := {}.

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
  Global Instance sem_ty_rec_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@sem_ty_rec Σ).
  Proof.
    intros C1 C2 HA.
    apply (fixpoint_ne (sem_ty_rec_pre C1) (sem_ty_rec_pre C2)); solve_proper.
  Qed.

  Global Instance sem_ty_prod_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sem_ty_prod Σ).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_sum_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sem_ty_sum Σ).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_arr_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sem_ty_arr Σ _).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_forall_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@sem_ty_forall Σ _).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_exist_proper :
    Proper (pointwise_relation _ (≡) ==>(≡)) (@sem_ty_exist Σ).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_ref_proper : Proper ((≡) ==> (≡)) (@sem_ty_ref Σ _).
  Proof. solve_proper. Qed.
  Global Instance sem_ty_rec_proper :
    Proper (pointwise_relation _ (≡) ==>(≡)) (@sem_ty_rec Σ).
  Proof.
    intros C1 C2 HA. apply equiv_dist=> n.
    apply sem_ty_rec_ne=> A. by apply equiv_dist.
  Qed.
End types_properties.
