From tutorial_popl20 Require Import language.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import adequacy.

(** Plan:

1. HeapLang is a untyped language. We first define a syntactic types and a
   syntactic typing judgment.

      Γ ⊢ₜ e : τ

2. Following Derek's talk, we define semantic typing in Iris:

      Γ ⊨ e : τ

3. We then prove the fundamental theorem:

      Γ ⊢ₜ e : τ  →  Γ ⊨ e : τ

   Every term that is syntactically typed, is also semantically typed

4. We prove safety of semantic typing:

     ∅ ⊨ e : τ  →  e is safe, i.e. cannot crash

5. We prove that we get more by showing that certain "unsafe" programs are also
   semantically typed
*)

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
    [∗ map] τ;v ∈ Γ;vs, interp τ v.

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

  Lemma sem_typed_unsafe_pure :
    ∅ ⊨ (if: #true then #13 else #13 #37) : TInt.
  Proof.
    iIntros "!#" (vs) "Hvs /=". wp_pures. auto.
  Qed.
End semtyp.

Notation "Γ ⊨ e : A" := (sem_typed Γ e A)
  (at level 74, e, A at next level).

Definition safe (e : expr) :=
  ∀ σ es' e' σ',
    rtc erased_step ([e], σ) (es', σ') →
    e' ∈ es' →
    is_Some (to_val e') ∨ reducible e' σ'.

Lemma sem_type_safety `{!heapPreG Σ} e τ :
  (∀ `{!heapG Σ}, ∅ ⊨ e : τ) → safe e.
Proof.
  intros Hty σ es' e' σ'.
  apply (heap_adequacy Σ NotStuck e σ (λ _, True))=> // ?.
  iDestruct (Hty $! ∅) as "#He".
  rewrite subst_map_empty. iApply (wp_wand with "(He [])").
  { rewrite /interp_env. auto. }
  auto.
Qed.

Lemma type_safety e τ : ∅ ⊢ₜ e : τ → safe e.
Proof.
  intros Hty. eapply (sem_type_safety (Σ:=heapΣ))=> ?.
  by apply fundamental.
Qed.
