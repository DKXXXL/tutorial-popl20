From solutions Require Export polymorphism.
From iris.heap_lang Require Export proofmode.
From iris.base_logic.lib Require Export invariants.

(** * Semantics types *)
(** In the file [types.v] we defined types syntactically, i.e. using the
inductive definition [ty] that enumerated the possible types. In semantic
typing, we take a more "extensional" view of typing---we model semantics types
as predicates over values, which describe what values belong to the type. In
this file, we define the type [sem_ty], together with some boilerplate for
various Coq related boilerplate. In the file [sem_type_formers.v] we then define
combinators on [sem_ty] for the various type formers. For example:

<<
  Definition sem_ty_unit : sem_ty Σ := SemTy (λ w, ⌜ w = #() ⌝)%I.
  Definition sem_ty_prod (A1 A2 : sem_ty Σ) : sem_ty Σ := SemTy (λ w,
    ∃ w1 w2, ⌜w = (w1, w2)%V⌝ ∧ A1 w1 ∧ A2 w2)%I.
>>

Subsequently, in the file [sem_typed.v] we define the semantic typing judgment
[Γ ⊨ e : τA, in the file [compatibility.v] we prove the semantic typing rules,
i.e. *compatibility lemmas*, in the file [interp.v] we show that any syntactic
type (of Coq type [ty]) can be interpreted as a semantic type, and in the
file [fundamental.v] we prove the **fundamental lemma**, i.e. that syntactic
typing [Γ ⊢ₜ e : τ] implies semantic typing [interp Γ ⊨ e : interp τ].

In order to define the type [sem_ty] of semantic types, we use Iris predicates
instead of ordinary Coq predicates. That is, we use [val → iProp Σ] instead of
[val → Prop]. The power of Iris's logic then allows us to define semantic type
formers for e.g., higher-order references and polymorphism, in an elegant way.

It is crucial for value semantics of types to be **persistent** predicates. This
is due to the fact that our type system (as opposed to substructural type
systems, e.g., affine type systems) allows values to be used multiple times.
Hence, the fact that a value belongs to the semantics of a type must be
duplicable, which is guaranteed by persistence. *)

(** Semantic types are defined using a record, which bundles an Iris predicate
[sem_ty_car : val → iProp Σ] together with a proof of persistence. *)
Record sem_ty Σ := SemTy {
  sem_ty_car :> val → iProp Σ;
  sem_ty_persistent v : Persistent (sem_ty_car v)
}.
Arguments SemTy {_} _%I {_}.
Arguments sem_ty_car {_} _ _ : simpl never.

(** Iris uses the type class [Persistent] to capture which propositions are
persistent. Record fields are not automatically declared as instances, so we
do that by hand. *)
Existing Instance sem_ty_persistent.

(** To obtain nice notations for the semantic types (as we will see in the file
[sem_type_formers.v]), we create a notation scope [sem_ty_scope] for semantic
types, which we bind to the type [sem_ty]. *)
Declare Scope sem_ty_scope.
Bind Scope sem_ty_scope with sem_ty.
Delimit Scope sem_ty_scope with sem_ty.

(** * The COFE structure on semantic types *)
(** We show that semantic types [sem_ty] form a Complete Ordered Family of
Equivalences (COFE). This is necessary mostly for enabling rewriting equivalent
semantic types through Coq's setoid rewrite system. This part is mostly
boilerplate. *)
Section sem_ty_cofe.
  Context {Σ : gFunctors}.

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
