From tutorial_popl20 Require Export types.

Inductive ty_unboxed : ty → Prop :=
  | TUnit_unboxed : ty_unboxed TUnit
  | TBool_unboxed : ty_unboxed TBool
  | TInt_unboxed : ty_unboxed TInt
  | TRef_unboxed τ : ty_unboxed (TRef τ).
Existing Class ty_unboxed.
Existing Instances TUnit_unboxed TBool_unboxed TInt_unboxed TRef_unboxed.

Inductive ty_un_op : un_op → ty → ty → Prop :=
  | Ty_un_op_int op : ty_un_op op TInt TInt
  | Ty_un_op_bool : ty_un_op NegOp TBool TBool.
Existing Class ty_un_op.
Existing Instances Ty_un_op_int Ty_un_op_bool.

Inductive ty_bin_op : bin_op → ty → ty → ty → Prop :=
  | Ty_bin_op_eq τ :
     ty_unboxed τ → ty_bin_op EqOp τ τ TBool
  | Ty_bin_op_arith op :
     TCElemOf op [PlusOp; MinusOp; MultOp; QuotOp; RemOp;
                  AndOp; OrOp; XorOp; ShiftLOp; ShiftROp] →
     ty_bin_op op TInt TInt TInt
  | Ty_bin_op_compare op :
     TCElemOf op [LeOp; LtOp] → ty_bin_op op TInt TInt TBool
  | Ty_bin_op_bool op :
     TCElemOf op [AndOp; OrOp; XorOp] → ty_bin_op op TBool TBool TBool.
Existing Class ty_bin_op.
Existing Instances Ty_bin_op_eq Ty_bin_op_arith Ty_bin_op_compare Ty_bin_op_bool.

Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).
Inductive typed (Γ : gmap string ty) : expr → ty → Prop :=
  (** Variables *)
  | Var_typed x τ :
     Γ !! x = Some τ →
     Γ ⊢ₜ Var x : τ
  (** Base tys *)
  | Unit_typed :
     Γ ⊢ₜ #() : TUnit
  | Bool_typed (b : bool) :
     Γ ⊢ₜ # b : TBool
  | Int_typed (i : Z) :
     Γ ⊢ₜ # i : TInt
  (** Products and sums *)
  | Pair_typed e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : τ1 → Γ ⊢ₜ e2 : τ2 →
     Γ ⊢ₜ Pair e1 e2 : TProd τ1 τ2
  | Fst_typed e τ1 τ2 :
     Γ ⊢ₜ e : TProd τ1 τ2 →
     Γ ⊢ₜ Fst e : τ1
  | Snd_typed e τ1 τ2 :
     Γ ⊢ₜ e : TProd τ1 τ2 →
     Γ ⊢ₜ Snd e : τ2
  | InjL_typed e τ1 τ2 :
     Γ ⊢ₜ e : τ1 →
     Γ ⊢ₜ InjL e : TSum τ1 τ2
  | InjR_typed e τ1 τ2 :
     Γ ⊢ₜ e : τ2 →
     Γ ⊢ₜ InjR e : TSum τ1 τ2
  | Case_typed e0 e1 e2 τ1 τ2 τ3 :
     Γ ⊢ₜ e0 : TSum τ1 τ2 → Γ ⊢ₜ e1 : TArr τ1 τ3 → Γ ⊢ₜ e2 : TArr τ2 τ3 →
     Γ ⊢ₜ Case e0 e1 e2 : τ3
  (** Functions *)
  | Rec_typed f x e τ1 τ2 :
     binder_insert f (TArr τ1 τ2) (binder_insert x τ1 Γ) ⊢ₜ e : τ2 →
     Γ ⊢ₜ Rec f x e : TArr τ1 τ2
  | App_typed e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : TArr τ1 τ2 → Γ ⊢ₜ e2 : τ1 →
     Γ ⊢ₜ App e1 e2 : τ2
  (** Polymorphic functions and existentials *)
  | TLam_typed e τ :
     ty_lift 0 <$> Γ ⊢ₜ e : τ →
     Γ ⊢ₜ (Λ: e) : TForall τ
  | TApp_typed e τ τ' :
     Γ ⊢ₜ e : TForall τ →
     Γ ⊢ₜ e <_> : ty_subst 0 τ' τ
  | Pack_typed e τ τ' :
     Γ ⊢ₜ e : ty_subst 0 τ' τ →
     Γ ⊢ₜ e : TExist τ
  | Unpack_typed e1 x e2 τ τ2 :
     Γ ⊢ₜ e1 : TExist τ →
     binder_insert x τ (ty_lift 0 <$> Γ) ⊢ₜ e2 : ty_lift 0 τ2 →
     Γ ⊢ₜ (unpack: x := e1 in e2) : τ2
  (** Heap operations *)
  | Alloc_typed e τ :
     Γ ⊢ₜ e : τ →
     Γ ⊢ₜ Alloc e : TRef τ
  | Load_typed e τ :
     Γ ⊢ₜ e : TRef τ →
     Γ ⊢ₜ Load e : τ
  | Store_typed e1 e2 τ :
     Γ ⊢ₜ e1 : TRef τ → Γ ⊢ₜ e2 : τ →
     Γ ⊢ₜ Store e1 e2 : TUnit
  | FAA_typed e1 e2 :
     Γ ⊢ₜ e1 : TRef TInt → Γ ⊢ₜ e2 : TInt →
     Γ ⊢ₜ FAA e1 e2 : TInt
  | CmpXchg_typed e1 e2 e3 τ :
     ty_unboxed τ →
     Γ ⊢ₜ e1 : TRef τ → Γ ⊢ₜ e2 : τ → Γ ⊢ₜ e3 : τ →
     Γ ⊢ₜ CmpXchg e1 e2 e3 : TProd τ TBool
  (** Operators *)
  | UnOp_typed op e τ σ :
     Γ ⊢ₜ e : τ →
     ty_un_op op τ σ →
     Γ ⊢ₜ UnOp op e : σ
  | BinOp_typed op e1 e2 τ1 τ2 σ :
     Γ ⊢ₜ e1 : τ1 → Γ ⊢ₜ e2 : τ2 →
     ty_bin_op op τ1 τ2 σ →
     Γ ⊢ₜ BinOp op e1 e2 : σ
  | If_typed e0 e1 e2 τ :
     Γ ⊢ₜ e0 : TBool → Γ ⊢ₜ e1 : τ → Γ ⊢ₜ e2 : τ →
     Γ ⊢ₜ If e0 e1 e2 : τ
  (** Fork *)
  | Fork_typed e :
     Γ ⊢ₜ e : TUnit →
     Γ ⊢ₜ Fork e : TUnit
where "Γ ⊢ₜ e : τ" := (typed Γ e τ).
