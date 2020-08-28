From iris.algebra Require Export list gmap.
From iris.heap_lang Require Export notation proofmode metatheory.
From iris.heap_lang.lib Require Export assert.

(** * Iris's HeapLang language *)
(** The Iris framework is parameterized by the language of program expressions
that one wishes to reason about, which makes it possible that the same logic
can be used for a wide variety of languages. For the purpose of the lecture
material, we consider the concurrent ML-style language *HeapLang*---the default
language shipped with the Iris Coq development. We use HeapLang instead of
defining our own language since the Iris development provides support for nice
syntax for HeapLang programs, contains a number of useful tactics for reasoning
about HeapLang programs, and contains a number of results about HeapLang's
metatheory (e.g. substitution).

While HeapLang itself is an untyped language, the purpose of this tutorial is
to define a type system for HeapLang, and then use semantic typing via logical
relations to prove type safety of HeapLang. Before we consider typing, we will
see the following in this file:

- How to write HeapLang programs.
- How to write specifications using weakest preconditions.
- How to use the Iris tactic language to prove such specifications.

Before we get started, let us give a brief overview of the features and syntax
of HeapLang:

- HeapLang has a substitution-based call-by-value semantics with a
  *right-to-left* evaluation order (inspired by OCaml and CakeML).
- HeapLang's values are either literals, products, sums, or functions.
  + Literals are denoted [# x] where [x] can be the unit (denoted [()]), a
    Boolean (of Coq type [bool]), an integer (of Coq type [Z]), or a location
    (of Coq type [loc]). Booleans can be eliminated using the conditional
    operator [if: e1 then e2 else e3]. HeapLang supports the various unary and
    binary operators, like [e1 + e2], [e1 * e2], etc.
  + Products can be introduced as [(e1,e2)], and sums can be introduced as
    [InjL e] or [InjR e]. Products can be eliminated using the projections
    [Fst e] and [Snd e], and sums can be eliminated using pattern-matching
    [match: e with InjL x => e1 | InjR x => e2 end].
  + The syntax for non-recursive functions is [λ: x, e] and that of recursive
    functions is [rec: f x := e]. Here (and also in [match:]), [f] and [x] can
    either be variable names (of Coq type [string]) or the *anonymous binder*
    denoted [<>].
- HeapLang has dynamically allocated references that can be created using the
  [ref e] construct (in fact, HeapLang also has arrays, but we ignore in this
  tutorial). Dereferencing is done using the load construct [! e], and storing
  is done using the store construct [e1 <- e2]. Like most ML-style languages,
  HeapLang is garbage collected. That is, there is no explicit [free] construct.
- Let bindings are written as [let: x := e1 in e2], and sequencing is written as
  [e1 ;; e2].
- HeapLang supports dynamic thread creation using the [Fork e] construct,
  which spawns a new thread [e], and returns the unit value [()]. To support
  synchronization between threads, HeapLang has the following constructs:
  + The "fetch-and-add" operation [FAA e1 e2], which atomically adds the integer
    [e2] to the integer stored at location [e1]. It returns the old value of
    the integer at location [e1].
  + The "compare-and-exchange" operation [CmpXchg e1 e2 e3], which compares the
    value of the location [e1] with the value [e2]. If they are equal, it
    replace the value of the location [e1] with [e3]. It returns a tuple with
    the old value of the location [e1], and a Boolean indicating whether the
    value of [e1] was equal to [e2]. Note that compare-and-exchange can only
    be used on unboxed values, i.e. values that fit into one machine word:
    the unit value, Booleans, integers, and locations.

Note that most of the HeapLang notations are designed to mimic Coq's syntax as
much as possible. However, to disambiguate HeapLang notation from Coq's, colons
[:] are added to many parts of the syntax. For example, one would write
[λ: x, e] and [let: x := e1 in e2].

More details about HeapLang can be found in the Iris Coq development. Most
importantly:

- The documentation of HeapLang:
  https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/heap_lang.md
- The syntax and operational semantics of the language:
  https://gitlab.mpi-sws.org/iris/iris/blob/master/theories/heap_lang/lang.v
- The notations for the various constructs:
  https://gitlab.mpi-sws.org/iris/iris/blob/master/theories/heap_lang/notation.v
*)

(** * Reasoning about HeapLang programs *)
(** We will now demonstrate how we can use Iris to prove properties about
HeapLang programs. For this, we make use of Iris's tactics for separation
logic, as provided by the *MoSeL proof mode* (formerly IPM, Iris Proof Mode).
Since the details of MoSeL are beyond the scope of this tutorial, we demonstrate
it in an example driven way. More information about MoSeL can be found at:

- The original paper POPL'17 about the Iris Proof Mode (IPM):
  https://robbertkrebbers.nl/research/articles/proofmode.pdf
- The ICFP'18 paper about MoSeL (which, among other things, made IPM parametric
  in the separation logic that is used):
  https://robbertkrebbers.nl/research/articles/mosel.pdf
- The overview of the MoSeL tactics:
  https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/proof_mode.md
- The overview of the MoSeL tactics for HeapLang:
  https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/heap_lang.md#tactics
*)

(** Let us start with a simple example: the function [swap] takes two locations,
and swaps their values: *)
Definition swap : val := λ: "l1" "l2",
  let: "x" := !"l1" in
  "l1" <- !"l2";;
  "l2" <- "x".

(** It is important to point out that programs in the HeapLang are written
using Coq definitions of type [val], the type of HeapLang values. Such
definitions are of type [val], instead of the type of HeapLang expressions
[expr], as it is assumed by HeapLang's substitution function ([subst]) that
values are closed, i.e. that substitution will not go into them. *)

(** Now that we have defined our first HeapLang program, let us write a
specification for using Iris's weakest preconditions: *)
Lemma wp_swap `{!heapG Σ} l1 l2 v1 v2 :
  l1 ↦ v1 -∗
  l2 ↦ v2 -∗
  WP swap #l1 #l2 {{ v, ⌜ v = #() ⌝ ∗ l1 ↦ v2 ∗ l2 ↦ v1 }}.
(** The lemma states that if [l1] and [l2] initially contain values the [v1] and
[v2], respectively, then after [swap #l1 #l2] has been executed, the values
of [l1] and [l2] have been swapped, i.e. they are [v2] and [v1], respectively.

This specification already points out a number of interesting features of
both separation logic and the Iris framework:

- First, a very technical one: each Iris lemma that involves HeapLang programs,
  should have the parameter [`{!heapG Σ}]. This has to do with Iris's generic
  infrastructure for handling ghost state. For now, these parameters can be
  ignored, but we will come back to them in the file [unsafe.v]. More
  information about the handling of ghost state in Iris can be found at:
  https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/proof_guide.md#resource-algebra-management
- More interestingly, this lemma makes use of the *points-to* or *maps-to*
  connective [l ↦ v] of separation logic. Here, [l] is a location (of Coq type
  [loc]) and [v] is a HeapLang value (of Coq type [val]). The points-to
  connective [l ↦ v] expressive exclusive ownership of the location [l], and
  states that the location has value [v].
- The Iris *weakest precondition* connective [WP e {{ v. Q }}] (of type
  [iProp Σ]) expresses that executing [e] is safe, and that when [e] returns a
  value [v], it satisfies the *postcondition* [Q] (note that [v] is a binder
  in [Q]).
- The points-to [l ↦ v] and weakest precondition [WP e {{ v, Q }}] connectives
  are not an ordinary Coq propositions (of type [Prop]), but are Iris
  propositions (of type [iProp Σ]).
- Iris lemmas look mostly identical to Coq lemmas (which is achieved by
  overloading the syntax of all logical connectives). However, in addition
  to the usual connectives from higher-order logic, they can also make use of
  the *separating conjunction* [P ∗ Q] and the *magic wand* [P -∗ Q]. Iris
  lemmas should start with a [P -∗ Q] at the top-level.
- Coq propositions [φ : Prop] can be embedded into Iris propositions using the
  syntax [⌜ φ ⌝]. In the lemma, we use the Coq's equality ([=]) in combination
  with the embedding to state that the return value of [swap] is the unit value.
*)

(** Now, let us see how we can prove the specification of [swap]. Like ordinary
Coq lemmas, we start a proof using the [Proof] command. *)
Proof.

(** This gives us a goal of the shape [.. -∗ .. -∗ WP ..]. Since this goal is
not an ordinary Coq goal, but an Iris goal, we make use of the MoSeL proof
mode tactics. We start by introducing the points-to assumptions [l1 ↦ v1] and
[l2 ↦ v2] into the MoSeL proof context using the [iIntros] tactic. *)
  iIntros "Hl1 Hl2".

(** At this point our goal is of the form [WP swap #l1 #l2 {{ .. ]}]. Let us
start by unfolding the definition of [swap]. For this, we make use of the
Ssreflect [rewrite] tactic (note: [rewrite /def] is like [unfold def], but
unlike [unfold], it can more easily be chained---which enables one to write more
compact proofs when considering more complicated lemmas). *)
  rewrite /swap.

(** At this point, our goal is [WP (λ: ..) .. {{ .. }}]. We now make use of the
tactic [wp_pures] to reduce pure redexes (β-reduction, but also reduction of
operators, etc.) in the goal. *)
  wp_pures.

(** At this point, the expression in evaluation position is [! #l1], i.e. a
load from the location [l1]. We make use of the tactic [wp_load]. This tactic
looks up the points-to connective [l1 ↦ v1] in the proof context, and replaces
[! #l1] by the value of [l1], i.e. [v1]. *)
  wp_load.

(** The next expression in evaluation position is [! #l2], so we use [wp_load]
again. Note that all [wp_]-tactics implicitly perform [wp_pures] first, so
there is no need to do that ourselves, but for clarity's sake it is sometimes
useful to do perform [wp_pures] manually. *)
  wp_load.

(** The next expression in evaluation position is [#l1 <- v2], i.e. a store
to the location [l1] with value [v2]. We make use of the tactic [wp_store],
which looks up the points-to connective [l1 ↦ v1] in the proof context, and
replaces it by [l1 ↦ v2]. Since the store operation returns the unit value,
the [#l1 <- v2] expression in the goal is replaced by [#()]. However, in this
case, the result of the expression in evaluation position ([#l1 <- v2]) is
unused (it appears in the LHS of HeapLang's sequencing operator [;;], so the
[;;] is immediately reduced. *)
  wp_store.

(** The next expression to consider is [#l2 <- v1]. We proceed as before, by
making use of the [wp_store] tactic. *)
  wp_store.

(** We have now reached the point where the [swap] function has returned. It
thus remains to prove the postcondition [⌜#() = #()⌝ ∗ l1 ↦ v2 ∗ l2 ↦ v1]. We
first make use of the [iFrame] tactic, which tries to *cancel out* as many
hypotheses from the MoSeL proof context in the goal. *)
  iFrame.

(** Since both hypotheses [l1 ↦ v2] and [l2 ↦ v1] appeared in the goal, we are
left with the goal [⌜#() = #()⌝]. We can now make use of the [iPureIntro] tactic,
which turn the MoSeL goal into the Coq goal [#() = #()]. Alternatively, we may
use the [auto] tactic, which performs [iPureIntro] implicitly, and finishes the
goal using Coq's [reflexivity] tactic. *)
  auto.
Qed.

(** ** Exercise (swap_and_add, easy) *)
(** Consider the following variant of the [swap] function: *)
Definition swap_and_add : val := λ: "l1" "l2",
  let: "x" := !"l1" in
  "l1" <- "x" + !"l2";;
  "l2" <- "x".

(** The specification is as follows: *)
Lemma wp_swap_and_add `{!heapG Σ} l1 l2 (x1 x2 : Z) :
  l1 ↦ #x1 -∗
  l2 ↦ #x2 -∗
  WP swap_and_add #l1 #l2 {{ v, ⌜ v = #() ⌝ ∗ l1 ↦ #(x1 + x2) ∗ l2 ↦ #x1 }}.
(** Note that since [swap_and_add] only works on integer values, we quantify
over integers [x1 x2 : Z] instead of values [v1 v2 : val] in the parameters of
the lemma. Furthermore, since we use integers, we need to make use of the
embedding [#] of literals, both in the program and in the points-to connectives.

You should prove this lemma.

Hint: [wp_pures] also executes the [+] operator. Carefully check how it affects
the embedded [#] and convince yourself why that makes sense. *)
(* SOLUTION *) Proof.
  iIntros. rewrite /swap_and_add. do 2 wp_load. do 2 wp_store. by iFrame.
Qed.

(** ** Reasoning about higher-order functions *)
(** For the next example, let us consider the higher-order function [twice].
This function takes a function [f] and a value [x] as its arguments, and applies
[f] twice to [x] *)
Definition twice : val := λ: "f" "x",
  "f" ("f" "x").

(** Since weakest-preconditions are first-class Iris propositions, we cannot
only use them in the conclusions of a lemma, but also in the premises, and in
nested ways. This is crucial to reason about higher-order functions. Let us see
that in action to give a specification of the [twice] function. *)
Lemma wp_twice `{!heapG Σ} (Ψ : val → iProp Σ) (vf vx : val) :
  WP vf vx {{ w, WP vf w {{ Ψ }} }} -∗
  WP twice vf vx {{ Ψ }}.

(** This lemma is quite a mouthful. First, it quantifies over an arbitrary
postcondition [Ψ : val → iProp Σ] (note, instead of writing [WP .. {{ v, Ψ v }}],
we may write [WP .. {{ Ψ }}]), and a HeapLang function value [vf]. In the
precondition of the lemma, it nests WP twice to account for the fact that
[twice] calls the function argument twice. *)
Proof.
(** The proof of this lemma proceeds in the usual way: we use [iIntros] to
introduce the premise into the MoSeL proof context, unfold the definition of
[twice] using [rewrite /twice], and then perform pure reductions using the
[wp_pures] tactic. *)
  iIntros "Hvf".
  rewrite /twice. wp_pures.

(** Our goal is now [WP vf (vf vx) {{ v, Ψ v }}]. To prove this goal, we make
use of the *bind* rule for weakest preconditions, which is:

<<
WP e {{ v, WP fill K v {{ Ψ }} }} -∗ WP fill K e {{ Ψ }}
>>

Here, [K] is a call-by-value (one-hole) evaluation context, and [fill K e] puts
[e] into the hole of [K]. The bind rule expresses that to prove [fill K e], we
should first prove [e], and then [fill K v] where [v] is the result of [e].

To use this rule, we make use of the [wp_bind e] tactic, which automatically
finds the context [K] given the expression [e]. *)
  wp_bind (vf vx).

(** At this point, the goal is precisely our hypothesis. We can thus finish the
proof by the [iAssumption] tactic, which is implicitly performed by [auto]. *)
  auto.
Qed.

(** To see [twice] in action, let us use it to implement the function [add_two],
which takes an integer value, and adds [2] to it. *)
Definition add_two : val := λ: "x",
  twice (λ: "y", #1 + "y") "x".

(** While this function is rather convoluted, the specification is precisely
what you would expect---it adds [2]. *)
Lemma wp_add_two `{!heapG Σ} (x : Z) :
  ⊢ WP add_two #x {{ w, ⌜ w = #(2 + x) ⌝ }}.
(** Note that this weakest precondition does not have a premise (i.e. the
lemma does not involve a magic wand [-∗] at the top-level, as we have seen in
previous examples). We thus use the scope [%I] ([I] of "Iris") to instruct Coq
to interpret this lemma as an Iris lemma. *)
Proof.
  rewrite /add_two. wp_pures.
(** We use the [iApply] tactic to make use of the specification [wp_twice] of
[twice] that we just proved. *)
  iApply wp_twice.

(** This turns the goal into two nested weakest preconditions, for the two calls
to the higher-order function [(λ: "y", #1 + "y")] to [x]. Since the function
is pure, [wp_pures] will reduce the entire program (it processes nested weakest
preconditions automatically. *)
  wp_pures.

(** The remaining goal is ⌜#(1 + (1 + x)) = #(2 + x)⌝, which can be solved by
the following tactic. *)
  auto with f_equal lia.

(** As usual, [auto] implicitly performs [iPureIntro]. The [with f_equal lia]
argument instructs [auto] to additionally use Coq's [f_equal] tactic when it is
faced a goal [f x1 .. xn = f y1 .. yn], which is turned into goals [xi = yi],
and Coq's [lia] tactic for linear integer arithmetic when it is faced a goal
on integers. *)
Qed.

(** ** Exercise (add_two_ref, moderate) *)
(** Instead of using [twice] to add [2] to an integer value, we now use it to
add [2] to the value of a reference to an integer. That is, we use [twice]
with a function that reads the reference and adds [1] to it. *)
Definition add_two_ref : val := λ: "l",
  twice (λ: <>, "l" <- #1 + !"l") #().

(** The specification is as expected (it follows the pattern we have seen in
e.g. [swap_and_add]---we make use of the points-to connective [l ↦ #x]. *)
Lemma wp_add_two_ref `{!heapG Σ} l (x : Z) :
  l ↦ #x -∗
  WP add_two_ref #l {{ w, ⌜ w = #() ⌝ ∗ l ↦ #(2 + x) }}%I.

(** You should complete this proof. Hint: you need to use the usual Coq lemmas
about addition on [Z] (or the [replace] or [rewrite (_ : x = y)] tactic with
[lia]) to turn [2 + x] into [1 + (1 + x)]. Tactics like [replace] and [rewrite]
work operate both on the MoSeL proof goal and the MoSeL proof context. *)
(* SOLUTION *) Proof.
  iIntros "Hl".
  rewrite /add_two_ref. wp_pures.
  iApply wp_twice.
  wp_load. wp_store.
  wp_load. wp_store.
  rewrite Z.add_assoc (_ : (1 + 1)%Z = 2) //.
  iFrame.
  auto.
Qed.

(** ** Reasoning about higher-order state *)
(** To see how Iris can be used to reason about higher-order state---that is,
references that contain functions---let us consider a variant of [twice] where
we do not pass the function and value directly, but instead pass them using a
reference. Moreover, instead of returning the result of applying the function
twice, it puts the result in the value reference. *)
Definition twice_ref : val := λ: "lf" "lx",
  "lx" <- !"lf" (!"lf" !"lx").

(** The specification of [twice_ref] follows that of [twice], but it quantifies
both over locations [lf] and [lx], and the HeapLang function [vf] and value [vx]
that they contain, respectively. *)
Lemma wp_twice_ref `{!heapG Σ} (Ψ : val → iProp Σ) lf lx (vf vx : val) :
  lf ↦ vf -∗
  lx ↦ vx -∗
  WP vf vx {{ w, WP vf w {{ w', lf ↦ vf -∗ lx ↦ w' -∗ Ψ #() }} }} -∗
  WP twice_ref #lf #lx {{ Ψ }}.
(** The postcondition of the weakest precondition in the premise is somewhat
more complicated. It makes use of the magic wand [-∗] to give back ownership of
the references [lf] and [lx] to the client of the lemma. Since the value of [lx]
has been changed to [w'], the points-to connective that is given back is
[lx ↦ w']. *)
Proof.
(** The beginning of the proof is as usual. *)
  iIntros "Hlf Hlx Hvf".
  rewrite /twice_ref. wp_pures.
  do 2 wp_load.
  wp_bind (vf vx).

(** We now end up in the critical part of the proof. Our goal is a weakest
precondition for [vf vx] and we also have a hypotheses that contains a weakest
precondition for [vf vx]. However, the postconditions of both weakest
preconditions do not match up. We make use of the lemma [wp_wand], which is the
weakest precondition-version of the rule of consequence for Hoare triples:

<<
  WP e {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e {{ Ψ }}
>>

We use the [with] argument of [iApply] to use the hypotheses [Hvf] containing
the weakest precondition for the first argument of [wp_wand]. *)
  iApply (wp_wand with "Hvf").

(** At this point, we need to show that the postcondition of the weakest
precondition from the hypothesis implies the postcondition of the weakest
precondition in the goal. *)
  iIntros (w) "Hvf".
  wp_load.
  wp_bind (vf w).
(** We are now in the same situation, we have to prove a weakest precondition
for [vf w], but the postcondition is different from the weakest precondition in
the hypothesis. We thus use [wp_wand] again. *)

  iApply (wp_wand with "Hvf").
  iIntros (w') "Hvf".

  wp_store.
  iApply ("Hvf" with "Hlf Hlx").
Qed.

(** ** Exercise (add_two_fancy, moderate) *)
Definition add_two_fancy : val := λ: "x",
  let: "lf" := ref (λ: "y", #1 + "y") in
  let: "lx" := ref "x" in
  twice_ref "lf" "lx";;
  !"lx".

Lemma wp_add_two_fancy `{!heapG Σ} (x : Z) :
  ⊢ WP add_two_fancy #x {{ w, ⌜ w = #(2 + x) ⌝ }}.
(* SOLUTION *) Proof.
  rewrite /add_two_fancy. wp_pures.
  wp_alloc lf as "Hlf".
  wp_alloc lx as "Hlx".
  wp_pures.
  wp_bind (twice_ref _ _).
  iApply (wp_twice_ref with "Hlf Hlx").
  wp_pures.
  iIntros "Hlx Hfx".
  wp_load.
  auto with f_equal lia.
Qed.

(** * Reasoning about "unsafe" programs *)
(** Since HeapLang is an untyped language, we can write down arbitrary
programs, i.e. programs that are not typeable by conventional type systems, and
prove logical specifications of them. We will show this on two small examples
that will use at other places in this tutorial to demonstrate the advances of
semantic typing. *)

(** The program below contains the expression [#13 #37] in the else-branch
of the conditional. The expression [#13 #37] will get stuck in the operational
semantics, i.e. it is unsafe. However, the else-branch is never executed, so we
can still show that this function is safe by proving a specification. *)
Definition unsafe_pure : val := λ: <>,
  if: #true then #13 else #13 #37.

Lemma wp_unsafe_pure `{!heapG Σ} :
  ⊢ WP unsafe_pure #() {{ v, ⌜ v = #13 ⌝ }}.
Proof.
  rewrite /unsafe_pure.
  wp_pures.
  auto.
Qed.

(** Exercise (unsafe_ref, easy) *)
(** The function below reuses a reference using values of different types. *)
Definition unsafe_ref : val := λ: <>,
  let: "l" := ref #0 in "l" <- #true;; !"l".

Lemma wp_unsafe_ref `{!heapG Σ} :
  ⊢ WP unsafe_ref #() {{ v, ⌜ v = #true ⌝ }}.
(* SOLUTION *) Proof.
  rewrite /unsafe_ref. wp_pures.
  wp_alloc l.
  wp_store.
  wp_load.
  auto.
Qed.
