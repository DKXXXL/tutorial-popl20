From tutorial_popl20 Require Import language.

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
    | _ => SemTy (λ _, False) (* dummy interpretation *)
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


(*  LocalWords:  Robbert
 *)
