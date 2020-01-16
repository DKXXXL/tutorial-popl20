From iris.algebra Require Export list gmap.
From iris.heap_lang Require Export lang notation metatheory.
From iris.heap_lang.lib Require Export assert.

(** We model type-level lambdas and applications as thunks since heap_lang does
not have them. *)
Notation "Λ: e" := (λ: <>, e)%E (at level 200, only parsing) : expr_scope.
Notation "Λ: e" := (λ: <>, e)%V (at level 200, only parsing) : val_scope.
Notation "e !" := (App e%E #()) (at level 10, only parsing) : expr_scope.

(** We wrap unpack into an explicitly function so that we can have a nice
notation for it. *)
Definition exist_unpack : val := λ: "x" "y", "x" "y".

Notation "'unpack:' x := e1 'in' e2" := (exist_unpack (Lam x%binder e2%E) e1%E)
  (at level 200, x at level 1, e1, e2 at level 200, only parsing,
   format "'[' 'unpack:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.

Notation "'unpack:' x := e1 'in' e2" := (exist_unpack (LamV x%binder e2%E) e1%E)
  (at level 200, x at level 1, e1, e2 at level 200, only parsing,
   format "'[' 'unpack:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : val_scope.
