From solutions Require Export sem_typed.

(** Semantic operator typing *)
Class SemTyUnboxed `{!heapG Σ} (A : sem_ty Σ) :=
  sem_ty_unboxed v :
    A v -∗ ⌜ val_is_unboxed v ⌝.

Class SemTyUnOp `{!heapG Σ} (op : un_op) (A B : sem_ty Σ) :=
  sem_ty_un_op v :
    A v -∗ ∃ w, ⌜ un_op_eval op v = Some w ⌝ ∧ B w.

Class SemTyBinOp `{!heapG Σ} (op : bin_op) (A1 A2 B : sem_ty Σ) :=
  sem_ty_bin_op v1 v2 :
    A1 v1 -∗ A2 v2 -∗ ∃ w, ⌜ bin_op_eval op v1 v2 = Some w ⌝ ∧ B w.

Section sem_operators.
  Context `{!heapG Σ}.
  Implicit Types A B : sem_ty Σ.

  (* Unboxed types *)
  Global Instance sem_ty_unit_unboxed : SemTyUnboxed ().
  Proof. by iIntros (v ->). Qed.
  Global Instance sem_ty_bool_unboxed : SemTyUnboxed sem_ty_bool.
  Proof. iIntros (v). by iDestruct 1 as (b) "->". Qed.
  Global Instance sem_ty_int_unboxed : SemTyUnboxed sem_ty_int.
  Proof. iIntros (v). by iDestruct 1 as (i) "->". Qed.
  Global Instance sem_ty_ref_unboxed A : SemTyUnboxed (ref A).
  Proof. iIntros (v). by iDestruct 1 as (i ->) "?". Qed.

  (* Operator typing *)
  Global Instance sem_ty_un_op_int op : SemTyUnOp op sem_ty_int sem_ty_int.
  Proof. iIntros (?). iDestruct 1 as (i) "->". destruct op; eauto. Qed.
  Global Instance sem_ty_un_op_bool : SemTyUnOp NegOp sem_ty_bool sem_ty_bool.
  Proof. iIntros (?). iDestruct 1 as (i) "->". eauto. Qed.

  Global Instance sem_ty_bin_op_eq A : SemTyUnboxed A → SemTyBinOp EqOp A A sem_ty_bool.
  Proof.
    iIntros (? v1 v2) "A1 _". rewrite /bin_op_eval /sem_ty_car /=.
    iDestruct (sem_ty_unboxed with "A1") as %Hunb.
    rewrite decide_True; last solve_vals_compare_safe.
    eauto.
  Qed.
  Global Instance sem_ty_bin_op_arith op :
    TCElemOf op [PlusOp; MinusOp; MultOp; QuotOp; RemOp;
                 AndOp; OrOp; XorOp; ShiftLOp; ShiftROp] →
    SemTyBinOp op sem_ty_int sem_ty_int sem_ty_int.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /sem_ty_car /=; eauto.
  Qed.
  Global Instance sem_ty_bin_op_compare op :
    TCElemOf op [LeOp; LtOp] →
    SemTyBinOp op sem_ty_int sem_ty_int sem_ty_bool.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /sem_ty_car /=; eauto.
  Qed.
  Global Instance sem_ty_bin_op_bool op :
    TCElemOf op [AndOp; OrOp; XorOp] →
    SemTyBinOp op sem_ty_bool sem_ty_bool sem_ty_bool.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /sem_ty_car /=; eauto.
  Qed.
End sem_operators.
