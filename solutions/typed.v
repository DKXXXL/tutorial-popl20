From solutions Require Export types polymorphism.

(** * Syntactic typing for HeapLang *)
(** In this file, we define a syntactic type system for HeapLang. We do this
in the conventional way by defining the typing judgment [Γ ⊢ₜ e : τ] using an
inductive relation. *)

(** * Operator typing *)
(** In order to define the typing judgment, we first need some helpers for
operator typing. *)

(** The first helper we define is [ty_unboxed τ], which expresses that values
of [τ] are unboxed, i.e. they fit into one machine word. This helper is needed
to state the typing rules for equality and compare-and-exchange ([CmpXchg]),
which can only be used on unboxed values. *)
Inductive ty_unboxed : ty → Prop :=
  | TUnit_unboxed : ty_unboxed TUnit
  | TBool_unboxed : ty_unboxed TBool
  | TInt_unboxed : ty_unboxed TInt
  | TRef_unboxed τ : ty_unboxed (TRef τ).

(** In order to let Coq automatically prove that types are unboxed, we turn
[ty_unboxed] into a type class, and turn the constructors into type class
instances. This is done using the following commands. *)
Existing Class ty_unboxed.
Existing Instances TUnit_unboxed TBool_unboxed TInt_unboxed TRef_unboxed.

(** We can now use Coq's type class inference mechanism to automatically
establish that given types are unboxed. This is done by invoking the [apply _]
tactic. *)
Lemma TRef_TRef_TInt_unboxed : ty_unboxed (TRef (TRef TInt)).
Proof. apply _. Qed.

(** The true power of turning [ty_unboxed] into a type class is that whenever a
lemma or definition has a [ty_unboxed] argument, type class inference is called
automatically. *)

(** The relation [ty_un_op op τ σ] expresses that a unary operator [op] with an
argument of type [τ] has result type [σ]. We also turn [ty_un_op] into a type
class. *)
Inductive ty_un_op : un_op → ty → ty → Prop :=
  | Ty_un_op_int op : ty_un_op op TInt TInt
  | Ty_un_op_bool : ty_un_op NegOp TBool TBool.
Existing Class ty_un_op.
Existing Instances Ty_un_op_int Ty_un_op_bool.

(** The relation [ty_bin_op op τ1 τ2 σ] expresses that a binary operator [op]
with arguments of type [τ1] and [τ2] has result type [σ]. In order to avoid
an abundance of rules, we factorize the operators into 4 categories: equality,
arithmetic, comparison, and Boolean operators. For the last 3 categories, we make
use of [TCElemOf x xs], where [x : A] and [xs : list A], which is a type class
version of [x ∈ xs]. *)
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

(** * The typing judgment *)
(** With the above helpers at hand, we can define the syntactic typing judgment
[Γ ⊢ₜ e : τ]. While most of the typing rules are standard, the definition
involves a number of interesting aspects.

- Since term-level variables in HeapLang are modeled using strings, we represent
  typing contexts [Γ : gmap string ty] as mappings from strings to types. Here,
  [gmap] is the type of generic maps from the std++ library.
- In addition to named binders, HeapLang also features the anonymous binder
  [<>]. This allows one to define [λ: x, e] as [rec: <> x := e]. Binders in
  HeapLang are of type [binder], whose definition is as follows:

  <<
  Inductive binder := BAnon : binder | BNamed : string → binder.
  >>

  As a result, in the typing rules of all constructs that involve binders (i.e.,
  the typing rules [Rec_typed] and [Unpack_typed]) we have to consider two
  cases [BAnon] and [BNamed]. To factorize these typing rules, we make use of
  [binder_insert], which lifts the insert operator [<[_:=_> _] on [gmap] to
  binders.
- The type of values [val] and expressions [expr] of HeapLang are defined in
  a mutually inductive fashion:

  <<
  Inductive expr :=
    (* Values *)
    | Val (v : val)
    (* Base lambda calculus *)
    | Var (x : string)
    | Rec (f x : binder) (e : expr)
    | App (e1 e2 : expr)
    (* Products *)
    | Pair (e1 e2 : expr)
    | Fst (e : expr)
    | Snd (e : expr)
    (* Sums *)
    | InjL (e : expr)
    | InjR (e : expr)
    | Case (e0 : expr) (e1 : expr) (e2 : expr)
    (* Etc. *)
  with val :=
    | LitV (l : base_lit)
    | RecV (f x : binder) (e : expr)
    | PairV (v1 v2 : val)
    | InjLV (v : val)
    | InjRV (v : val).
  >>

  For technical reasons, the only terms that are considered values are those
  that begin with the [Val] expression former. This means that, for example,
  [Pair (Val v1) (Val v2)] is not a value---it reduces to [Val (PairV v1 v2)],
  which is. This leads to some administrative redexes, and to a distinction
  between "value pairs", "value sums", "value closures" and their "expression"
  counterparts.

  However, this also makes values syntactically uniform, which we exploit in the
  definition of substitution ([subst]), which just skips over [Val] terms,
  because values should be closed, and hence not affected by substitution. As a
  consequence, we can entirely avoid talking about "closed terms" in the
  definition of HeapLang.

  As a result of the mutual inductive definition, and the distinction between
  "value pairs", "value sums", "value closures" and their "expression"
  counterparts, we need to define the typing judgment in a mutual inductive
  fashion too. Hence, apart from the judgment [Γ ⊢ₜ e : τ], we have the judgment
  [⊢ᵥ v : τ]. Note that since values are supposed to be closed, the latter
  judgment does not have a context [Γ].
*)

(** We use [Reserved Notation] so we can use the notation already in the
definition of the typing judgment. *)
Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).
Reserved Notation "⊢ᵥ v : τ" (at level 20, v, τ at next level).

Inductive typed : gmap string ty → expr → ty → Prop :=
  (** Variables *)
  | Var_typed Γ x τ :
     Γ !! x = Some τ →
     Γ ⊢ₜ Var x : τ
  (** Values *)
  | Val_typed Γ v τ :
     ⊢ᵥ v : τ →
     Γ ⊢ₜ v : τ
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
  | InjL_typed Γ e τ1 τ2 :
     Γ ⊢ₜ e : τ1 →
     Γ ⊢ₜ InjL e : TSum τ1 τ2
  | InjR_typed Γ e τ1 τ2 :
     Γ ⊢ₜ e : τ2 →
     Γ ⊢ₜ InjR e : TSum τ1 τ2
  | Case_typed Γ e0 e1 e2 τ1 τ2 τ3 :
     Γ ⊢ₜ e0 : TSum τ1 τ2 → Γ ⊢ₜ e1 : TArr τ1 τ3 → Γ ⊢ₜ e2 : TArr τ2 τ3 →
     Γ ⊢ₜ Case e0 e1 e2 : τ3
  (** Functions *)
  | Rec_typed Γ f x e τ1 τ2 :
     binder_insert f (TArr τ1 τ2) (binder_insert x τ1 Γ) ⊢ₜ e : τ2 →
     Γ ⊢ₜ Rec f x e : TArr τ1 τ2
  | App_typed Γ e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : TArr τ1 τ2 → Γ ⊢ₜ e2 : τ1 →
     Γ ⊢ₜ App e1 e2 : τ2
  (** Polymorphic functions and existentials *)
  | TLam_typed Γ e τ :
     ty_lift 0 <$> Γ ⊢ₜ e : τ →
     Γ ⊢ₜ (Λ: e) : TForall τ
  | TApp_typed Γ e τ τ' :
     Γ ⊢ₜ e : TForall τ →
     Γ ⊢ₜ e <_> : ty_subst 0 τ' τ
  | Pack_typed Γ e τ τ' :
     Γ ⊢ₜ e : ty_subst 0 τ' τ →
     Γ ⊢ₜ (pack: e) : TExist τ
  | Unpack_typed Γ e1 x e2 τ τ2 :
     Γ ⊢ₜ e1 : TExist τ →
     binder_insert x τ (ty_lift 0 <$> Γ) ⊢ₜ e2 : ty_lift 0 τ2 →
     Γ ⊢ₜ (unpack: x := e1 in e2) : τ2
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
  | FAA_typed Γ e1 e2 :
     Γ ⊢ₜ e1 : TRef TInt → Γ ⊢ₜ e2 : TInt →
     Γ ⊢ₜ FAA e1 e2 : TInt
  | CmpXchg_typed Γ e1 e2 e3 τ :
     ty_unboxed τ →
     Γ ⊢ₜ e1 : TRef τ → Γ ⊢ₜ e2 : τ → Γ ⊢ₜ e3 : τ →
     Γ ⊢ₜ CmpXchg e1 e2 e3 : TProd τ TBool
  (** Recursive types *)
  | Fold_typed Γ e τ :
     Γ ⊢ₜ e : ty_subst 0 (TRec τ) τ →
     Γ ⊢ₜ (fold: e) : TRec τ
  | Unfold_typed Γ e τ :
     Γ ⊢ₜ e : TRec τ →
     Γ ⊢ₜ (unfold: e) : ty_subst 0 (TRec τ) τ
  (** Operators *)
  | UnOp_typed Γ op e τ σ :
     Γ ⊢ₜ e : τ →
     ty_un_op op τ σ →
     Γ ⊢ₜ UnOp op e : σ
  | BinOp_typed Γ op e1 e2 τ1 τ2 σ :
     Γ ⊢ₜ e1 : τ1 → Γ ⊢ₜ e2 : τ2 →
     ty_bin_op op τ1 τ2 σ →
     Γ ⊢ₜ BinOp op e1 e2 : σ
  | If_typed Γ e0 e1 e2 τ :
     Γ ⊢ₜ e0 : TBool → Γ ⊢ₜ e1 : τ → Γ ⊢ₜ e2 : τ →
     Γ ⊢ₜ If e0 e1 e2 : τ
  (** Fork *)
  | Fork_typed Γ e :
     Γ ⊢ₜ e : TUnit →
     Γ ⊢ₜ Fork e : TUnit
with val_typed : val → ty → Prop :=
  (** Base types *)
  | UnitV_typed :
     ⊢ᵥ #() : TUnit
  | BoolV_typed (b : bool) :
     ⊢ᵥ #b : TBool
  | IntV_val_typed (i : Z) :
     ⊢ᵥ #i : TInt
  (** Products and sums *)
  | PairV_typed v1 v2 τ1 τ2 :
     ⊢ᵥ v1 : τ1 → ⊢ᵥ v2 : τ2 →
     ⊢ᵥ PairV v1 v2 : TProd τ1 τ2
  | InjLV_typed v τ1 τ2 :
     ⊢ᵥ v : τ1 →
     ⊢ᵥ InjLV v : TSum τ1 τ2
  | InjRV_typed v τ1 τ2 :
     ⊢ᵥ v : τ2 →
     ⊢ᵥ InjRV v : TSum τ1 τ2
  (** Functions *)
  | RecV_typed f x e τ1 τ2 :
     binder_insert f (TArr τ1 τ2) (binder_insert x τ1 ∅) ⊢ₜ e : τ2 →
     ⊢ᵥ RecV f x e : TArr τ1 τ2
  | TLamV_typed e τ :
     ∅ ⊢ₜ e : τ →
     ⊢ᵥ (Λ: e) : TForall τ
where "Γ ⊢ₜ e : τ" := (typed Γ e τ)
and "⊢ᵥ v : τ" := (val_typed v τ).

(** * Exercise (suger_typed, easy) *)
(** To make it possible to write programs in a compact way, HeapLang features
the following syntactic sugar:

<<
(λ: x, e)              := (rec: <> x := e)
(let: x := e1 in e2)   := (λ x, e2) e1
(e1 ;; e2)             := (let: <> := e1 in e2)
Skip                   := (λ: <>, #()) #()
>>

Prove the following derived typing rules for the syntactic sugar. Note that
due to the distinction between expressions and values, you have to prove some
of them for both the expression construct and their value counterpart. *)

Lemma Lam_typed Γ x e τ1 τ2 :
  binder_insert x τ1 Γ ⊢ₜ e : τ2 →
  Γ ⊢ₜ (λ: x, e) : TArr τ1 τ2.
(* SOLUTION *) Proof.
  intros He.
  apply Rec_typed.
  simpl.
  done.
Qed.

Lemma LamV_typed x e τ1 τ2 :
  binder_insert x τ1 ∅ ⊢ₜ e : τ2 →
  ⊢ᵥ (λ: x, e) : TArr τ1 τ2.
(* SOLUTION *) Proof.
  intros He.
  apply RecV_typed.
  simpl.
  done.
Qed.

Lemma Let_typed Γ x e1 e2 τ1 τ2 :
  Γ ⊢ₜ e1 : τ1 →
  binder_insert x τ1 Γ ⊢ₜ e2 : τ2 →
  Γ ⊢ₜ (let: x := e1 in e2) : τ2.
(* SOLUTION *) Proof.
  intros He1 He2.
  apply App_typed with τ1.
  - by apply Lam_typed.
  - done.
Qed.

Lemma Seq_typed Γ e1 e2 τ1 τ2 :
  Γ ⊢ₜ e1 : τ1 →
  Γ ⊢ₜ e2 : τ2 →
  Γ ⊢ₜ (e1;; e2) : τ2.
(* SOLUTION *) Proof.
  intros He1 He2.
  by apply Let_typed with τ1.
Qed.

Lemma Skip_typed Γ :
  Γ ⊢ₜ Skip : ().
(* SOLUTION *) Proof.
  apply App_typed with ()%ty.
  - apply Val_typed, RecV_typed. apply Val_typed, UnitV_typed.
  - apply Val_typed, UnitV_typed.
Qed.

(** * Typing of concrete programs *)
(** ** Exercise (swap_typed, easy) *)
(** Prove that the non-polymorphic swap function [swap] can be given the type
[ref τ → ref τ → ()] for any [τ]. *)
Lemma swap_typed τ : ⊢ᵥ swap : (ref τ → ref τ → ()).
(* SOLUTION *) Proof.
  rewrite /swap.
  apply LamV_typed.
  apply Lam_typed.
  apply Let_typed with τ.
  { apply Load_typed. by apply Var_typed. }
  apply Seq_typed with ()%ty.
  { apply Store_typed with τ.
    - by apply Var_typed.
    - apply Load_typed. by apply Var_typed. }
  apply Store_typed with τ.
  - by apply Var_typed.
  - by apply Var_typed.
Qed.

(** ** Exercise (swap_poly_typed, easy) *)
(** Prove that [swap_poly] can be typed using the polymorphic type
[∀ X, ref X → ref X → ())], i.e. [∀: ref #0 → ref #0 → ())] in De Bruijn style. *)
Lemma swap_poly_typed : ⊢ᵥ swap_poly : (∀: ref #0 → ref #0 → ()).
(* SOLUTION *) Proof.
  rewrite /swap_poly.
  apply TLamV_typed.
  do 2 apply Lam_typed.
  apply Let_typed with (#0)%ty.
  { apply Load_typed. by apply Var_typed. }
  apply Seq_typed with ()%ty.
  { apply Store_typed with (#0)%ty.
    - by apply Var_typed.
    - apply Load_typed. by apply Var_typed. }
  apply Store_typed with (#0)%ty.
  - by apply Var_typed.
  - by apply Var_typed.
Qed.

(** ** Exercise (not_typed, easy) *)
(** Prove that the programs [unsafe_pure] and [unsafe_ref] from [language.v]
cannot be typed using the syntactic type system. *)
Lemma unsafe_pure_not_typed τ : ¬ (⊢ᵥ unsafe_pure : τ).
(* SOLUTION *) Proof.
  intros Htyped.
  repeat
    match goal with
    | H : _ ⊢ₜ _ : _ |- _ => inversion H; simplify_eq/=; clear H
    | H : ⊢ᵥ _ : _ |- _ => inversion H; simplify_eq/=; clear H
    end.
Qed.

Lemma unsafe_ref_not_typed τ : ¬ (⊢ᵥ unsafe_ref : τ).
(* SOLUTION *) Proof.
  intros Htyped.
  repeat
    match goal with
    | H : _ ⊢ₜ _ : _ |- _ => inversion H; simplify_eq/=; clear H
    | H : ⊢ᵥ _ : _ |- _ => inversion H; simplify_eq/=; clear H
    end; simplify_map_eq; congruence.
Qed.
