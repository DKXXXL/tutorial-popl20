From tutorial_popl20 Require Export language.

(** * Polymorphic functions in HeapLang *)
(** We model type-level lambdas and applications as thunks since heap_lang does
not have them. *)
Notation "Λ: e" := (λ: <>, e)%E (at level 200, only parsing) : expr_scope.
Notation "Λ: e" := (λ: <>, e)%V (at level 200, only parsing) : val_scope.
Notation "e '<_>'" := (App e%E #()) (at level 10, only parsing) : expr_scope.

(** We wrap [pack] and [unpack] into an explicitly function so that we can have
a nice notation for it. *)
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

Definition swap_poly : val := Λ: λ: "l1" "l2",
  let: "x" := !"l1" in
  "l1" <- !"l2";;
  "l2" <- "x".

Lemma wp_swap_poly `{!heapG Σ} l1 l2 v1 v2 :
  l1 ↦ v1 -∗
  l2 ↦ v2 -∗
  WP swap_poly <_> #l1 #l2 {{ v, ⌜ v = #() ⌝ ∗ l1 ↦ v2 ∗ l2 ↦ v1 }}.
(* REMOVE *) Proof.
  iIntros "Hl1 Hl2".
  rewrite /swap_poly.
  wp_pures.
  wp_load.
  (* wp_pures is performed implicitly, so not needed *)
  wp_load.
  wp_store.
  wp_store.
  iFrame.
  auto.
Qed.
