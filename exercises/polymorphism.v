From exercises Require Export language.

(** * Polymorphic, existential and recursive types in HeapLang *)
(** In order to define a type system for HeapLang (in the file [typed.v]), we
need to extend HeapLang with constructs for polymorphic functions (i.e.,
type-level lambdas and application), existential types (i.e., pack and
unpack), and iso-recursive types (i.e., fold and unfold). Since HeapLang is an
untyped language, it does natively have these constructs. *)

(** We retrofit type-level lambdas and application on HeapLang by defining them
as mere thunks, and ordinary application, respectively. This ensures that
polymorphic programs satisfy a **value restriction**, which is needed to obtain
type safety in the presence of mutable state. *)
Notation "Λ: e" := (λ: <>, e)%E (at level 200, only parsing) : expr_scope.
Notation "Λ: e" := (λ: <>, e)%V (at level 200, only parsing) : val_scope.
Notation "e '<_>'" := (App e%E #()) (at level 10, only parsing) : expr_scope.

(** We also use ordinary lambdas and application to retrofit [pack] and
[unpack] on HeapLang. This time we first define some helper functions so that
we can have a nice notation for these constructs. *)
Definition exist_pack : val := λ: "x", "x".
Definition exist_unpack : val := λ: "x" "y", "x" "y".

Notation "'pack:' e" := (exist_pack e%E)
  (at level 200, e at level 200,
   format "'[' 'pack:'  e ']'") : expr_scope.

Notation "'unpack:' x := e1 'in' e2" := (exist_unpack (Lam x%binder e2%E) e1%E)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'unpack:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.
Notation "'unpack:' x := e1 'in' e2" := (exist_unpack (LamV x%binder e2%E) e1%E)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'unpack:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : val_scope.

(** And we apply the trick one more to retrofit [fold] and [unfold] on
HeapLang. *)
Definition rec_fold : val := λ: "x", "x".
Definition rec_unfold : val := λ: "x", "x".

Notation "'fold:' e" := (rec_fold e%E)
  (at level 200, e at level 200,
   format "'[' 'fold:'  e ']'") : expr_scope.

Notation "'unfold:' e" := (rec_unfold e%E)
  (at level 200, e at level 200,
   format "'[' 'unfold:'  e ']'") : expr_scope.

(** ** Exercise (swap_poly, easy) *)
(** Below we define a polymorphic version of the [swap] function. *)
Definition swap_poly : val := Λ: λ: "l1" "l2",
  let: "x" := !"l1" in
  "l1" <- !"l2";;
  "l2" <- "x".

(** Prove the following specification. *)
Lemma wp_swap_poly `{!heapG Σ} l1 l2 v1 v2 :
  l1 ↦ v1 -∗
  l2 ↦ v2 -∗
  WP swap_poly <_> #l1 #l2 {{ v, ⌜ v = #() ⌝ ∗ l1 ↦ v2 ∗ l2 ↦ v1 }}.
Proof.
  (* exercise *)
Admitted.
