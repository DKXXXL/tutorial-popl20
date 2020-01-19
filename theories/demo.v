From tutorial_popl20 Require Import language.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import adequacy.

Inductive ty :=
  | TUnit : ty
  | TBool : ty
  | TInt : ty
  | TProd : ty → ty → ty
  | TArr : ty → ty → ty
  | TRef : ty → ty.

Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).

Inductive typed : gmap string ty → expr → ty → Prop :=
  (** Variables *)
  | Var_typed Γ x τ :
     Γ !! x = Some τ →
     Γ ⊢ₜ Var x : τ
  (** Base values *)
  | UnitV_typed Γ :
     Γ ⊢ₜ #() : TUnit
  | BoolV_typed Γ (b : bool) :
     Γ ⊢ₜ #b : TBool
  | IntV_val_typed Γ (i : Z) :
     Γ ⊢ₜ #i : TInt
  (** Products and sums *)
  | Pair_typed Γ e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : τ1 → Γ ⊢ₜ e2 : τ2 →
     Γ ⊢ₜ Pair e1 e2 : TProd τ1 τ2
  | Fst_typed Γ e τ1 τ2 :
     Γ ⊢ₜ e : TProd τ1 τ2 →
     Γ ⊢ₜ Fst e : τ1
  | Snd_typed Γ e τ1 τ2 :
     Γ ⊢ₜ e : TProd τ1 τ2 →
     Γ ⊢ₜ Snd e : τ2
  (** Functions *)
  | Rec_typed Γ f x e τ1 τ2 :
     binder_insert f (TArr τ1 τ2) (binder_insert x τ1 Γ) ⊢ₜ e : τ2 →
     Γ ⊢ₜ Rec f x e : TArr τ1 τ2
  | App_typed Γ e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : TArr τ1 τ2 → Γ ⊢ₜ e2 : τ1 →
     Γ ⊢ₜ App e1 e2 : τ2
  (** Heap operations *)
  | Alloc_typed Γ e τ :
     Γ ⊢ₜ e : τ →
     Γ ⊢ₜ Alloc e : TRef τ
  | Load_typed Γ e τ :
     Γ ⊢ₜ e : TRef τ →
     Γ ⊢ₜ Load e : τ
  | Store_typed Γ e1 e2 τ :
     Γ ⊢ₜ e1 : TRef τ → Γ ⊢ₜ e2 : τ →
     Γ ⊢ₜ Store e1 e2 : TUnit
  (** If *)
  | If_typed Γ e0 e1 e2 τ :
     Γ ⊢ₜ e0 : TBool → Γ ⊢ₜ e1 : τ → Γ ⊢ₜ e2 : τ →
     Γ ⊢ₜ If e0 e1 e2 : τ
where "Γ ⊢ₜ e : τ" := (typed Γ e τ).

(**

  We have already seen syntactic typing (introduced by Robbert):

    Γ ⊢ e : T

  Goal: define semantic typing (introduced by Derek):

    Γ ⊨ e : T

Plan:

step 1:
  Define value interpretation for types (for closed values):

  〚T〛: val → iProp

step 2: Lift value interpretation to expressions (semantic typing judgment):

- We first define a simplified version for closed expressions

   ∅ ⊨ e : T := WP e {{ w, 〚T〛w }}

- Then, we define full version:

   Γ ⊨ e : T := ∀ vs, 〚Γ〛vs → WP susbst vs e {{ w, 〚T〛w }}

*)

Section semtyp.
  Context `{!heapG Σ}.

  Record sem_ty := SemTy {
    sem_ty_car :> val → iProp Σ;
    sem_ty_persistent v : Persistent (sem_ty_car v)
  }.
  Arguments SemTy _%I {_}.
  Existing Instance sem_ty_persistent.

  Fixpoint interp (τ : ty) : sem_ty :=
    match τ with
    | TUnit => SemTy (λ w, ⌜w = #()⌝)
    | TBool => SemTy (λ w, ⌜w = #true⌝ ∨ ⌜w = #false⌝)
    | TInt => SemTy (λ w, ∃ n : Z, ⌜w = #n⌝ )
    | TProd τ1 τ2 =>
      SemTy (λ w, ∃ v1 v2, ⌜w = (v1, v2)%V⌝ ∗ interp τ1 v1 ∗ interp τ2 v2)
    | TArr τ1 τ2 => SemTy (λ w, □ ∀ v, interp τ1 v -∗ WP w v {{ u, interp τ2 u}})
    | TRef τ => SemTy (λ w, ∃ l : loc,
       ⌜ w = #l ⌝ ∗ inv (nroot .@ "ref" .@ l) (∃ v, l ↦ v ∗ interp τ v))
    end%I.

  Definition interp_env (Γ : gmap string ty) (vs : gmap string val) : iProp Σ :=
    [∗ map] x ↦ τ;v ∈ Γ;vs, interp τ v.

  Definition sem_typed (Γ : gmap string ty) (e : expr) (τ : ty) : iProp Σ :=
    □ ∀ vs, interp_env Γ vs -∗ WP subst_map vs e {{ w, interp τ w }}.

  Notation "Γ ⊨ e : A" := (sem_typed Γ e A)
    (at level 74, e, A at next level).

  Lemma Pair_sem_typed Γ e1 e2 τ1 τ2 :
    Γ ⊨ e1 : τ1 -∗ Γ ⊨ e2 : τ2 -∗ Γ ⊨ Pair e1 e2 : TProd τ1 τ2.
  Proof.
    iIntros "#He1 #He2".
    rewrite /sem_typed.
    iIntros "!#".
    iIntros (vs) "#Hvs".
    simpl.
    wp_bind (subst_map vs e2).
    iApply wp_wand.
    { by iApply "He2". }
    iIntros (w2) "Hw2".
    wp_bind (subst_map vs e1).
    iApply wp_wand.
    { by iApply "He1". }
    iIntros (w1) "Hw1".
    wp_pures.
    iExists w1, w2. iFrame. auto.
  Restart.
    iIntros "#He1 #He2 !#" (vs) "#Hvs /=".
    wp_apply (wp_wand with "(He2 [$])").
    iIntros (w2) "Hw2".
    wp_apply (wp_wand with "(He1 [$])").
    iIntros (w1) "Hw1".
    wp_pures; eauto.
  Qed.

  Theorem fundamental Γ e τ : Γ ⊢ₜ e : τ → Γ ⊨ e : τ.
  Proof.
    intros Htyped. iInduction Htyped as [] "IH".
    5:{ iApply Pair_sem_typed; auto. }
  Admitted.

  Definition unsafe_pure : val := λ: <>,
    if: #true then #13 else #13 #37.
  Lemma sem_typed_unsafe_pure :
    ∅ ⊨ unsafe_pure : TArr TUnit TInt.
  Proof.
  Admitted.
End semtyp.

Notation "Γ ⊨ e : A" := (sem_typed Γ e A)
  (at level 74, e, A at next level).

Lemma sem_type_safety `{!heapPreG Σ} e σ es σ' e' τ :
  (∀ `{!heapG Σ}, ∅ ⊨ e : τ) →
  rtc erased_step ([e], σ) (es, σ') → e' ∈ es →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hty.
  apply (heap_adequacy Σ NotStuck e σ (λ _, True))=> // ?.
  iDestruct (Hty $! ∅) as "#He".
  rewrite subst_map_empty. iApply (wp_wand with "(He [])").
  { rewrite /interp_env. auto. }
  auto.
Qed.

Lemma type_safety e σ es σ' e' τ :
  (∅ ⊢ₜ e : τ) →
  rtc erased_step ([e], σ) (es, σ') → e' ∈ es →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hty. eapply (sem_type_safety (Σ:=heapΣ))=> ?.
  by apply fundamental.
Qed.

(*  LocalWords:  Robbert
 *)
