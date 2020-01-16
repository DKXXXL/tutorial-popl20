From tutorial_popl20 Require Export base.
From iris.heap_lang Require Export proofmode.
From iris.base_logic.lib Require Export invariants.

(* The domain of semantic types: persistent Iris predicates over values *)
Record sem_ty Σ := SemTy {
  sem_ty_car :> val → iProp Σ;
  sem_ty_persistent v : Persistent (sem_ty_car v)
}.
Arguments SemTy {_} _%I {_}.
Arguments sem_ty_car {_} _ _ : simpl never.
Bind Scope sem_ty_scope with sem_ty.
Delimit Scope sem_ty_scope with sem_ty.
Existing Instance sem_ty_persistent.

(* The COFE structure on semantic types *)
Section sem_ty_cofe.
  Context `{Σ : gFunctors}.

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
