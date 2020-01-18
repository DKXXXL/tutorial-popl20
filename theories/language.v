From iris.algebra Require Export list gmap.
From iris.heap_lang Require Export notation proofmode metatheory.
From iris.heap_lang.lib Require Export assert.

Definition swap : val := λ: "l1" "l2",
  let: "x" := !"l1" in
  "l1" <- !"l2";;
  "l2" <- "x".

Lemma swap_wp `{heapG Σ} l1 l2 v1 v2 :
  l1 ↦ v1 -∗
  l2 ↦ v2 -∗
  WP swap #l1 #l2 {{ v, ⌜ v = #() ⌝ ∗ l1 ↦ v2 ∗ l2 ↦ v1 }}.
Proof.
  iIntros "Hl1 Hl2".
  rewrite /swap.
  wp_pures.
  wp_load.
  (* wp_pures is performed implicitly, so not needed *)
  wp_load.
  wp_store.
  wp_store.
  iFrame.
  auto.
Qed.

Definition twice : val := λ: "f" "x",
  "f" ("f" "x").

Lemma twice_wp `{heapG Σ} (Ψ : val → iProp Σ) (vf vx : val) :
  WP vf vx {{ w, WP vf w {{ Ψ }} }} -∗
  WP twice vf vx {{ Ψ }}.
Proof.
  iIntros "Hvf".
  rewrite /twice. wp_pures.
  wp_bind (vf vx).
  auto.
Qed.

Definition add_two : val := λ: "x",
  twice (λ: "y", #1 + "y") "x".

Lemma add_two_wp `{heapG Σ} (x : Z) :
  WP add_two #x {{ w, ⌜ w = #(2 + x) ⌝ }}%I.
Proof.
  rewrite /add_two. wp_pures.
  iApply twice_wp. wp_pures.
  iPureIntro. auto with f_equal lia.
Qed.

Definition add_two_ref : val := λ: "l",
  twice (λ: <>, "l" <- #1 + !"l") #().

Lemma add_two_ref_wp `{heapG Σ} l (x : Z) :
  l ↦ #x -∗
  WP add_two_ref #l {{ w, ⌜ w = #() ⌝ ∗ l ↦ #(2 + x) }}%I.
Proof.
  iIntros "Hl".
  rewrite /add_two_ref. wp_pures.
  iApply twice_wp.
  wp_load. wp_store.
  wp_load. wp_store.
  rewrite Z.add_assoc (_ : (1 + 1) = 2) //.
  iFrame.
  auto.
Qed.

Definition twice_ref : val := λ: "lf" "lx",
  !"lf" (!"lf" !"lx").

Lemma twice_ref_wp `{heapG Σ} (Ψ : val → iProp Σ) lf lx (vf vx : val) :
  lf ↦ vf -∗
  lx ↦ vx -∗
  WP vf vx {{ w, WP vf w {{ Ψ }} }} -∗
  WP twice_ref #lf #lx {{ Ψ }}.
Proof.
  iIntros "Hlf Hlx Hvf".
  rewrite /twice_ref. wp_pures.
  do 2 wp_load.
  wp_bind (vf vx).
  iApply (wp_wand with "Hvf").
  iIntros (w) "Hvf".
  wp_load.
  auto.
Qed.

Definition add_two_2 : val := λ: "x",
  let: "lx" := ref "x" in
  let: "lf" := ref (λ: "y", #1 + "y") in
  twice_ref "lf" "lx".

Lemma add_two_2_wp `{heapG Σ} (x : Z) :
  WP add_two_2 #x {{ w, ⌜ w = #(2 + x) ⌝ }}%I.
Proof.
  rewrite /add_two_2. wp_pures.
  wp_alloc lx as "Hlx".
  wp_alloc lf as "Hfx".
  wp_pures.
  iApply (twice_ref_wp with "Hfx Hlx").
  wp_pures.
  iPureIntro. auto with f_equal lia.
Qed.

(** UNSAFE *)
Definition unsafe_pure : val := λ: <>,
  if: #true then #13 else #13 #37.

Lemma unsafe_pure_wp `{heapG Σ} :
  WP unsafe_pure #() {{ v, ⌜ v = #13 ⌝ }}%I.
Proof.
  rewrite /unsafe_pure.
  wp_pures.
  auto.
Qed.

Definition unsafe_ref : val := λ: <>,
  let: "l" := ref #0 in "l" <- #true;; !"l".

Lemma unsafe_ref_wp `{heapG Σ} :
  WP unsafe_ref #() {{ v, ⌜ v = #true ⌝ }}%I.
Proof.
  rewrite /unsafe_ref. wp_pures.
  wp_alloc l.
  wp_store.
  wp_load.
  auto.
Qed.

(** Polymorphism *)
(** We model type-level lambdas and applications as thunks since heap_lang does
not have them. *)
Notation "Λ: e" := (λ: <>, e)%E (at level 200, only parsing) : expr_scope.
Notation "Λ: e" := (λ: <>, e)%V (at level 200, only parsing) : val_scope.
Notation "e '<_>'" := (App e%E #()) (at level 10, only parsing) : expr_scope.

Definition swap_poly : val := Λ: λ: "l1" "l2",
  let: "x" := !"l1" in
  "l1" <- !"l2";;
  "l2" <- "x".

Lemma swap_poly_wp `{heapG Σ} l1 l2 v1 v2 :
  l1 ↦ v1 -∗
  l2 ↦ v2 -∗
  WP swap_poly <_> #l1 #l2 {{ v, ⌜ v = #() ⌝ ∗ l1 ↦ v2 ∗ l2 ↦ v1 }}.
Proof.
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

(** We wrap unpack into an explicitly function so that we can have a nice
notation for it. *)
Definition exist_unpack : val := λ: "x" "y", "x" "y".

Notation "'unpack:' x := e1 'in' e2" := (exist_unpack (Lam x%binder e2%E) e1%E)
  (at level 200, x at level 1, e1, e2 at level 200, only parsing,
   format "'[' 'unpack:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.

Notation "'unpack:' x := e1 'in' e2" := (exist_unpack (LamV x%binder e2%E) e1%E)
  (at level 200, x at level 1, e1, e2 at level 200, only parsing,
   format "'[' 'unpack:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : val_scope.
