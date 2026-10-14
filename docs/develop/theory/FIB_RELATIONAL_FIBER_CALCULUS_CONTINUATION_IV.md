# FIB Relational Fiber Calculus · Continuation IV
## —Realizable ExactChart interfaces, complete event languages, and a conditional resource frontier

> **Machine contract.** This is a `generic-v1` theory reference volume. It is
> append-only: the definitions and results in this file are ordinary
> mathematical prose, and later corrections belong after the final append
> anchor. The text is not a Lean source and makes no kernel-verification claim.

Continuation III gave a finite chart interface, but two of its hypotheses need
to be made operational before a controller or a resource frontier can be
extracted. A successor written as `Next_e(i,x)` may depend on a hidden source
even when the reply is identical, and a response-phase count need not bound the
ordered events between two replies. This continuation makes those obligations
explicit. It is a narrow adapter: it does not construct an ExactChart for an
arbitrary signed FIB fiber.

## 41. A realizable ExactChart/controller interface

**Definition 41.1 (typed source chart).** Let

$$
D=\bigsqcup_{i\in I}D_i,
\qquad
D_i=\{(i,x):X_i(x)\},
$$

where $I$ is finite and each $X_i$ is a Presburger-definable set of natural
parameters. A point $s=(i,x)$ denotes one complete source. Chart coordinates
are a description of $s$; they are not an online source-identity port.

**Definition 41.2 (complete boundary and its fiber).** A semantic execution
boundary has the form

$$
b=(e,j,H,v,p,Y),
$$

where $e$ is the controller position, $j$ is the actual epoch, $H$ is the raw
ordered event trace on one source, $v\in\mathbb N^d$ is the complete resource
vector, $p\in\{\mathsf{pending},\mathsf{complete}\}$, and $Y$ is the complete
terminal row when $p=\mathsf{complete}$ (and is $\bot$ while pending). The
boundary map is written $\operatorname{bd}_s$. Its fiber is

$$
F_b=\{s:\operatorname{bd}_s=b\}.
$$

The trace $H$, epoch, resource vector, pending/complete flag, and terminal row
are retained as one same-source record. A boundary is never assembled by taking
the trace from one source and the row or cost vector from another.

**Definition 41.3 (realizable ExactChart/controller).** Fix finite controller
positions $E$, reply alphabet $O$, and primitive action alphabet $A$. A chart
contract is *realizable* when it supplies the following data.

1. At every legal read position $e$, the literal reply is
   $\operatorname{Reply}_e(s,j)\in O$, and there is one source-independent
   transition
   $\delta_e:O\to E$ such that
   $\operatorname{Next}_e(s,j)=\delta_e(\operatorname{Reply}_e(s,j))$.
   Thus successor choice factors through the observed reply (equivalently,
   through the observable boundary fiber), not through a hidden chart point.
2. For every boundary fiber and action $a$, legality is common:
   $a$ is legal for one member of $F_b$ exactly when it is legal for every
   member. The action may still receive different legal replies; the set of
   legal actions is the shared part.
3. Every reply, successor, resource increment, epoch update, and terminal row
   is evaluated on the same source $s$. All cross-source comparisons use the
   complete $Y$, not a projection of it.
4. The controller instruction at $e$ is a fixed primitive action or halt. Its
   reply branches use the corresponding $\delta_e$ (and the analogous
   source-independent factorization for any action that returns an observation).

The first two clauses are the missing realizability conditions for a finite
chart table. A finite image cover or a separately witnessed coordinate does
not satisfy them.

**Counterexample 41.4 (identical replies with a source-dependent successor).**
Take $I=\{0,1\}$, $X_0=X_1=\{\ast\}$, $O=\{0\}$ and controller positions
$e,h_0,h_1$. At $e$ the only legal read returns $0$ on both sources, but

$$
\operatorname{Next}_e(0,\ast)=h_0,
\qquad
\operatorname{Next}_e(1,\ast)=h_1.
$$

Let $h_0$ and $h_1$ halt with distinct complete rows $Y_0\ne Y_1$. Any
function $\delta_e$ sends the common reply $0$ to one position. Sending it to
$h_0$ is wrong on source $1$, and sending it to $h_1$ is wrong on source $0$.
The table is therefore a finite pseudo-controller with identical replies, not a
realizable controller. The obstruction is the hidden source-dependent
successor, not the size of the chart.

## 42. Response phases do not bound raw event histories

**Definition 42.1 (phase count and raw event history).** For a run $\pi$, let
$q_r(\pi)$ count response-producing phases. The notation $q_r+1$ includes the
terminal phase. The raw history is instead the ordered word

$$
H(\pi)=h_1h_2\cdots h_m
$$

over events carrying their action, epoch, reply (when present), and resource
increment. It includes passive actions and interventions, repeated reads,
zero-reply events, and the complete terminal event. In general
$q_r(\pi)+1$ is only a projection of $H(\pi)$.

**Definition 42.2 (independent event bound).** For a controller bound $K$ and
budget $B$, an *event horizon* is an independently certified finite number
$T_K(B)$ such that every successful run of every $K$-position controller within
budget $B$ has $|H(\pi)|\le T_K(B)$. The certificate is separate from the
response-phase count. As an alternative, a *certified regular history encoding*
is a finite automaton for the exact ordered histories together with an effective
well-founded-rank or exact acceleration certificate that decides termination,
terminal rows, and resource maxima. Plain regularity without this certificate
does not provide a finite synthesis problem.

**Counterexample 42.3 (constant replies and a zero-cost cycle).** Let one
position $e$ permit a passive action $p$ that returns no reply, costs
$0\in\mathbb N^d$, and loops to $e$, followed by a read returning the constant
reply $0$ and a halt. At the action-language level, every word
$p^m\,\mathsf{read}\,\mathsf{halt}$ is legal. These words all have the same
response-phase count $q_r+1=2$, while their ordered histories have lengths
$m+2$. The passive loop can also be taken forever, with the same phase count
and no complete boundary. Consequently $q_r+1$ cannot replace $T_K(B)$: even
the zero-cost case has unbounded ordered histories and admits nontermination.

## 43. The full action language and safe factorization

**Definition 43.1 (full legal action language).** Let

$$
A=A_{\mathsf{read}}\sqcup A_{\mathsf{passive}}
  \sqcup A_{\mathsf{intervene}}\sqcup\{\mathsf{halt}\}.
$$

For a source $s$, $\mathcal W_s\subseteq A^*$ is the language of all finite
legal words, including every allowed interleaving of passive and intervention
actions with reads and updates. Legality is checked at each boundary using the
common-fiber rule of Definition 41.3. A controller selects one word online by
its fixed positions and observed replies; it does not select a different source
or chart after an event.

**Definition 43.2 (exact source/action semantics).** For $s$ and
$w\in\mathcal W_s$, write

$$
\operatorname{Exec}(s,w)=
\bigl(H_s(w),j_s(w),v_s(w),p_s(w),Y_s(w)\bigr).
$$

Every component is computed from the same $s$ and the ordered word $w$. A
controller policy $\pi$ has an exact factorization when its run on $s$ is

$$
\operatorname{Run}_\pi(s)=
\bigl(s,w_s,\operatorname{Exec}(s,w_s)\bigr),
\qquad w_s\in\mathcal W_s,
$$

and the next action at a shared boundary is the same function of that boundary
and its reply for every $s\in F_b$.

**Theorem 43.3 (safe factorization by a well-founded rank).** Suppose a finite
controller satisfies the realizable ExactChart conditions, and suppose there
is a rank $\rho$ from pending boundaries to a well-founded ordered set such
that every nonterminal legal event sends $b$ to $b'$ with
$\rho(b')<\rho(b)$. Suppose also that all sources reaching one terminal
position have the same complete row there. Then every source has one finite
same-source action word $w_s\in\mathcal W_s$, the controller halts, and its
terminal row is the complete target row of $s$.

Conversely, an exact source/action factorization with common legality, the
reply-factorized transitions, the terminal-row condition, and this rank is a
realizable controller witness.

**Proof.** At a pending boundary, common legality gives one admissible action
set on the entire fiber. The factorized transition and the actual reply select
one next position, so induction on events gives a unique execution on the same
source. Strict rank decrease rules out an infinite event sequence. At a halt,
the complete-row condition makes the installed row equal to the source's
target row. The converse follows by the same induction: the exact predicates
reproduce each event of the factorized word, and rank proves that its terminal
event is reached. At no step are two source witnesses spliced together. $\square$

## 44. Conditional resource feasibility and its Pareto basis

**Definition 44.1 (resource frontier).** Assume $D\ne\varnothing$. Let
$\mathcal C_K$ be the controllers with at most $K$ positions that are legal,
finite-terminating and correct on every source in $D$. For $C\in\mathcal C_K$,
let $c_C(s)\in\mathbb N^d$ be its full vector of actual event costs on source
$s$, and put

$$
b(C)=\sup_{s\in D}c_C(s),
\qquad
\mathcal F_K=\{B\in\mathbb N^d:\exists C\in\mathcal C_K,\ b(C)\le B\}.
$$

The supremum is coordinatewise. A same-run weighted objective is defined
separately below.

**Theorem 44.2 (conditional decidability and effective frontier).** Assume:

1. $K$, the chart types, action types, reply types, and controller positions
   are finite;
2. an independent finite horizon $T_K(B)$ is available for every finite or
   mixed budget $B\in(\mathbb N\cup\{\infty\})^d$ that has at least one
   constrained coordinate, or a certified regular history encoding from
   Definition 42.2 is available;
3. admission, reply, legality, successor, epoch, exact cost, and complete-row
   equality predicates are Presburger-definable in the chart parameters and
   epoch; and
4. either a finite feasible seed controller is supplied, or an all-infinite
   synthesis extractor decides the unconstrained case and returns a finite
   controller when one exists.

Then budget feasibility $\operatorname{Feas}_K(B)$ is decidable. If it is
nonempty, $\mathcal F_K$ has a finite effectively computable Pareto basis
$\mathcal B_K$ and

$$
\mathcal F_K=\uparrow\mathcal B_K
 =\{B:\exists v\in\mathcal B_K, v\le B\}.
$$

**Proof.** Enumerate the finitely many controller graphs with at most $K$
positions and the finitely many action and reply labels. For a fixed graph,
enumerate its exact ordered paths of length at most $T_K(B)$. A path predicate
conjoins the chart admission formula, the same-source reply and legality tests,
the factorized successor equations, complete-row equality at shared halts, and
the pathwise vector-cost inequalities. All of these are Presburger by
assumption, and there are finitely many paths. Presburger quantifier
elimination therefore decides the finite disjunction over graphs and extracts
a controller when true. The certified regular alternative supplies the same
finite decision through its exact history summaries.

Feasibility is upward closed. For a finite list $A$ of feasible vectors, define
$\uparrow A=\{x:\exists v\in A,\ v\le x\}$. If $0\in A$, then
$\uparrow A=\mathbb N^d$ and the negative test is immediately false. For every
nonzero $v\in A$ choose $f(v)$ with $v_{f(v)}>0$ and form mixed boxes

$$
B_i^f=\min\{v_i-1:f(v)=i\},
\qquad \min\varnothing=\infty.
$$

The exact negative test is

$$
\exists x\in\mathcal F_K\setminus\uparrow A
\quad\Longleftrightarrow\quad
\bigvee_f\operatorname{Feas}_K(B^f).
$$

If the test is true, extract a feasible vector outside $\uparrow A$, search its
finite lower box for a componentwise-minimal feasible vector, and append that
vector to $A$. If the test is false, $A$ is complete. Dickson's lemma forbids
an infinite antichain of appended vectors, so the exact negative test
terminates. The finite seed starts this loop; the all-infinite extractor either
supplies its first finite vector or proves that the basis is empty. $\square$

**Definition 44.3 (same-run weighted cost).** For
$\lambda\in\mathbb Q_{\ge 0}^d$, define

$$
W_\lambda(C)=\sup_{s\in D}\sum_{r=1}^d\lambda_r c_{C,r}(s).
$$

Finite path synthesis decides $W_\lambda(C)\le z$ by putting the weighted sum
inside each path predicate before taking the maximum over paths.

**Counterexample 44.4 (coordinatewise maxima do not scalarize a run).** Let
one controller have two sources with costs

$$
c_C(s_1)=(1,0),\qquad c_C(s_2)=(0,1).
$$

Then $b(C)=(1,1)$, but for $\lambda=(1,1)$ the same-run value is
$W_\lambda(C)=1$, whereas $\lambda\cdot b(C)=2$. Coordinatewise maxima, and
coordinatewise minima found by separate witnesses, cannot replace the pathwise
sum on one source.

**Counterexample 44.5 (separate policy minima are unattainable).** Suppose
one policy has worst vector $(2,0)$ and another has worst vector $(1,1)$.
The coordinatewise minima suggest $(1,0)$, but neither policy has that vector.
The pair $(1,0)$ is therefore not a feasible budget unless a third policy is
separately exhibited. A resource frontier must retain each complete policy and
its same-source traces before taking minima.

**Corollary 44.6 (weighted threshold attainment).** Under the hypotheses of
Theorem 44.2, fix $\lambda\in\mathbb Q_{\ge 0}^d$ and choose
$M\in\mathbb N_{>0}$ with $M\lambda\in\mathbb N^d$. The set

$$
\widetilde{\mathcal W}_{K,\lambda}
=\{z\in\mathbb N:\exists C\in\mathcal C_K,
                         M W_\lambda(C)\le z\}
$$

is upward closed and decidable by the same path predicates with the weighted
sum inserted before the source maximum. If it is nonempty, it has a least
element attained by a controller, and division by $M$ gives the exact rational
optimum. This scalar optimum is computed by its own threshold search; it is
not obtained by taking $\lambda\cdot v$ for a coordinatewise Pareto vector
$v$.

## 45. Adapter boundary and verification status

This adapter is distinct from [Native Resource Frontier](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RESOURCE_FRONTIER.md): that volume assumes the supplied native tree correspondence, fixed `Read/ApplyRho/Halt` tables, and its native paid-length horizon. It is also distinct from [CRF](RECURSIVE_RELATIONAL_OBSERVATION_CONSTRUCTOR_RESOURCE_FRONTIER.md): CRF assumes an accepted constructor-elimination family and its inherited chart bijection. The present interface supplies neither native-tree identities nor constructor elimination, and it permits the full passive/intervention action language. Those volumes can discharge the present hypotheses in their own scopes; this adapter does not replace their proofs.

Constructing a realizable ExactChart with source-total charts, common legality,
same-source ordered histories, full terminal rows, and Presburger exact costs
for a general signed FIB fiber remains open. In particular, finite image covers,
constant replies, or a proof of $\forall h\,\exists\delta_h$ do not establish a
single all-epoch controller. The statements above are ordinary mathematics and
have no Lean/kernel verification in this volume.

**文献表态。** Presburger decidability, effective semilinear descriptions and
Dickson's well-quasi-order principle are literature-attested background. The
source/action factorization, the two counterexamples, and the conditional
resource adapter are repo-derived ordinary mathematics. No literature priority
claim is made for this formulation.

**本批不主张的。** The phase bound $qr+1$ is not an event horizon; a finite
image cover is not a same-source witness; and a successful ExactChart interface
does not construct the interface for an arbitrary signed fiber. No physical
clock, reset, actuator, unrestricted action language, global controller-size
optimization or Lean/kernel theorem is supplied here.

## 追加锚（本行以下为增补区）

## 46. Execution-boundary corrections

The preceding sections are read with the following corrections. They close
three independent gaps: silent actions must not carry a hidden source-dependent
controller successor, a mixed budget must not turn an unbounded worst
coordinate into a finite frontier point, and a finite path enumeration must
prove source-total termination rather than enumerate only runs already known
to succeed.

**Definition 46.1 (all-action reply factorization).** Put

$$
O_\bot=O\sqcup\{\bot\}.
$$

For every primitive action, including read, passive, intervention, update and
any other non-halt action, write its response as

$$
\operatorname{Reply}_{e,a}(s,j)\in O_\bot.
$$

The value $\bot$ is the declared response of a silent action; it is not an
unobserved side channel. For every legal action there must be a single map

$$
\delta_{e,a}:O_\bot\to E
$$

such that

$$
\operatorname{Next}_{e,a}(s,j)
   =\delta_{e,a}(\operatorname{Reply}_{e,a}(s,j)).
$$

Thus the controller position after *every* action factors through the actual
visible response, with silent actions factoring through $\bot$. Legality is
constant on a complete boundary fiber, and the reply, successor, resource
increment, epoch update, stop flag and terminal row are all evaluated on the
same source and ordered event. This all-action condition supersedes the
read-only restriction in Definition 41.3. A source-dependent update of the
hidden physical state is allowed only when it does not make the controller
position or its next instruction source-dependent.

**Theorem 46.2 (corrected realizability implication).** Theorem 43.3 remains
valid after replacing its reply-factorization hypothesis by Definition 46.1.
In particular, a silent passive or intervention action cannot select two
different halt positions merely because two hidden sources share the same
visible boundary. Conversely, a source/action factorization is a controller
witness only when it includes a finite position set, the all-action maps
$\delta_{e,a}$, and a fixed instruction at each position. An arbitrary policy
or a list of source-indexed words is not by itself a finite controller.

The proof is the same induction on ordered events, now applied to every
action. The source-independent map $\delta_{e,a}$ supplies the unique next
instruction; same-source evaluation supplies the physical successor and full
terminal row; the rank excludes infinite event sequences.

**Definition 46.3 (finite resource frontier and mixed feasibility).** A
controller may have finite cost on every individual source while its
coordinatewise worst cost over an infinite source domain is unbounded. Define

$$
\mathcal C_K^{\mathrm{fin}}
 =\{C\in\mathcal C_K:b(C)\in\mathbb N^d\},
$$

$$
\mathcal F_K^{\mathrm{fin}}
 =\{B\in\mathbb N^d:\exists C\in\mathcal C_K^{\mathrm{fin}},\ b(C)\le B\}.
$$

For a mixed budget $\bar B\in(\mathbb N\cup\{\infty\})^d$, use the
finite-profile predicate

$$
\operatorname{Feas}^{\mathrm{fin}}_K(\bar B)
\iff
\exists x\in\mathbb N^d,
\quad x\le\bar B\quad\land\quad x\in\mathcal F_K^{\mathrm{fin}}.
$$

An $\infty$ coordinate therefore removes a constraint; it does not license an
infinite worst coordinate as a member of the finite frontier. If an
all-infinite synthesis procedure is used, it must either return a controller
with a finite profile or report that only unbounded profiles were found.

**Theorem 46.4 (corrected mixed-box test).** The Dickson/Pareto construction
in Theorem 44.2 applies to $\mathcal F_K^{\mathrm{fin}}$ and uses
$\operatorname{Feas}^{\mathrm{fin}}_K$ in every mixed box. For a finite current
basis $A\subseteq\mathcal F_K^{\mathrm{fin}}$, the negative test is

$$
\exists x\in\mathcal F_K^{\mathrm{fin}}\setminus\uparrow A
\quad\Longleftrightarrow\quad
\bigvee_f\operatorname{Feas}^{\mathrm{fin}}_K(B^f).
$$

The assertion is about finite Pareto points only. A controller with profile
$b(C)=(0,\infty)$ can satisfy an uncorrected mixed predicate while
contributing no vector to $\mathcal F_K^{\mathrm{fin}}$; it must not make the
negative test true. For example, on $D=\mathbb N$ a source can require
$n+1$ legal events before a final read, giving finite cost per source but an
unbounded worst cost. This is a valid termination behavior and still lies
outside the finite frontier.

**Definition 46.5 (source-total horizon certificate).** A finite synthesis
certificate for a budget $\bar B$ must apply to every admitted source, not
only to paths that have already been classified as successful. It consists of

1. full source coverage: every $s\in D$ satisfies the admission predicate and
   belongs to at least one enumerated ordered-history case;
2. all-response coverage: every response, including $\bot$ and every failure
   response allowed by the contract, has its successor case;
3. common legality and all-action reply factorization from Definition 46.1;
4. a terminal event with the complete same-source row on every admitted run;
5. a well-founded rank that strictly decreases on every actual nonterminal
   successor, or an exact regular-history acceleration certificate with the
   same termination and maximum-cost guarantee.

The resulting Presburger sentence has the form

$$
\forall s\in D\;\exists h\in\mathcal H_{\le T}:\quad
\operatorname{Run}_C(s)=h\ \land\operatorname{Terminal}(h)\ \land
Y_C(s)=Y_{\mathrm{target}}(s)\ \land c_C(s)\le\bar B,
$$

with the path partition and response successor equations included in the
certificate. A controller is admitted to $\mathcal C_K^{\mathrm{fin}}$ only
after this universal source-total and termination condition has been proved.

**Theorem 46.6 (sound finite synthesis after the correction).** Under the
finite chart, action and reply assumptions of Theorem 44.2, if a
source-total horizon or certified regular-history certificate is supplied,
and all predicates above are Presburger-definable, finite-budget feasibility
and the finite Pareto basis are decidable by the stated finite enumeration.

**Proof.** The certificate makes the path family finite and complete: no
admitted source, response branch, or nonterminal extension is omitted. The
universal source formula therefore decides legality, termination, terminal-row
equality and the actual same-source cost bound for each finite controller
graph. Presburger elimination decides that formula. Upward closure and
Dickson's lemma then compute the finite Pareto basis, using
$\operatorname{Feas}^{\mathrm{fin}}_K$ for mixed boxes. \(\square\)

Finally, $q_r+1$ is a terminal-run convention: it counts response-producing
phases together with the terminal phase only when a terminal event exists. An
infinite passive loop has no terminal phase, so the notation does not assign
it a completed phase count. In either case, it does not bound the raw ordered
event history.

## 47. Uniform finite-profile and history-state correction

The finite-profile restriction in Definition 46.3 must also be present in the
certificate used to decide mixed feasibility. Per-source finite termination
alone is insufficient on an infinite source domain.

**Definition 47.1 (bounded-profile certificate).** In addition to the clauses
of Definition 46.5, a certificate for a finite-profile controller supplies a
single vector

$$
x\in\mathbb N^d
$$

such that

$$
\forall s\in D,\qquad c_C(s)\le x,
$$

and, for a requested budget $\bar B$,

$$
x\le\bar B.
$$

Thus the finite feasibility sentence is existential in one finite vector and
universal over sources:

$$
\exists x\in\mathbb N^d\;\exists C\;\Bigl[
 x\le\bar B\ \land\ C\text{ is source-total and correct}\ \land
 \forall s\in D\;c_C(s)\le x\Bigr].
$$

This is the operational content of $C\in\mathcal C_K^{\mathrm{fin}}$; it
cannot be inferred from the separate facts that every source run terminates
and every individual cost is finite. The family with source $n\in\mathbb N$
and cost $n+1$ is the counterexample: it is source-total but has no such
finite $x$.

**Definition 47.2 (uniform horizon or exact acceleration).** The finite path
form of the synthesis test is permitted only when the supplied horizon is
uniform over every admitted source and response branch:

$$
\exists T\in\mathbb N\;\forall s\in D,
\quad |H_C(s)|\le T.
$$

Alternatively, an exact regular-history acceleration certificate must itself
decide source-total termination, the terminal row and the finite vector bound
$c_C(s)\le x$ without replacing the missing uniform horizon by a merely
per-source rank argument. A rank proves well-foundedness; it yields a finite
path enumeration only when its certificate also supplies a uniform bound or an
effective acceleration with these outputs.

**Theorem 47.3 (sound corrected feasibility statement).** Theorem 46.6 is
sound after requiring both a bounded-profile certificate and either a uniform
finite horizon or the full exact acceleration of Definition 47.2. The
Presburger decision then ranges over controller graphs, $x\in\mathbb N^d$,
and the universal source/response coverage formula. The mixed-box test uses
$\operatorname{Feas}^{\mathrm{fin}}_K$ and therefore cannot be witnessed by a
controller whose worst profile is infinite in any coordinate.

When history affects a future response, the arguments of
$\operatorname{Reply}_{e,a}$ and $\operatorname{Next}_{e,a}$ in Definition
46.1 are understood to include the complete current boundary, including the
ordered history $H$ (or an exact sufficient history state). The factorization
requirement is unchanged: after that complete state is fixed, the controller
position successor still factors only through the declared visible response,
including $\bot$ for a silent action.

## 48. Supersession and the all-infinite query

For the avoidance of a false mixed-budget reading, Definitions 46.3 and 47.1
are normative for this volume. They **supersede** the unqualified frontier and
feasibility sentences in Definitions 44.1 and Theorem 44.2: every occurrence
of $\mathcal F_K$ and $\operatorname{Feas}_K$ in that theorem is to be read as
$\mathcal F_K^{\mathrm{fin}}$ and
$\operatorname{Feas}_K^{\mathrm{fin}}$, with the bounded-profile and
source-total certificates of Sections 46--47. A per-source terminating
controller with an infinite coordinate is not a feasible finite-frontier
witness.

The all-infinite box is therefore a genuine decision query, not an
unbounded search instruction. The hypothesis corresponding to item 4 of
Theorem 44.2 is strengthened to:

$$
\operatorname{Feas}^{\mathrm{fin}}_K((\infty,\ldots,\infty))
$$

is decided by an exact finite-profile synthesis or by a proof that no finite
profile exists. “No finite controller has been found” is not a negative
answer. Once this all-infinite query is decided, the mixed-box extraction may
start with a finite witness or terminate with an empty finite Pareto basis;
the Dickson argument then concerns only the finite vectors in
$\mathcal F_K^{\mathrm{fin}}$.

The ambient type of the unbounded coordinatewise supremum is

$$
b(C)=\sup_{s\in D}c_C(s)\in(\mathbb N\cup\{\infty\})^d.
$$

Membership in $\mathcal C_K^{\mathrm{fin}}$ means exactly that this extended
supremum happens to lie in the finite subspace $\mathbb N^d$. This typing is
part of the correction: it makes the distinction between finite budget
feasibility and merely sourcewise finite execution explicit.

## 49. Explicit finite-feasibility alias

For every subsequent occurrence in this volume, define the formerly
abbreviated predicate by the explicit alias

$$
\operatorname{Feas}_K(\bar B) :=\
\operatorname{Feas}^{\mathrm{fin}}_K(\bar B).
$$

The finite synthesis sentence behind this alias quantifies a controller graph
with $|E|\le K$, its fixed instruction and all-action factorization maps, and
a finite vector $x\in\mathbb N^d$ satisfying $x\le\bar B$. It conjoins common
legality, source-total all-response coverage, terminal-row equality, the
uniform-history or exact-acceleration certificate, and

$$
\forall s\in D,\qquad c_C(s)\le x.
$$

Consequently, the alias is a finite-profile decision predicate rather than a
search that may silently return an unbounded coordinate. The Pareto basis and
all mixed-box statements in Sections 44--48 use this explicit predicate.

## 50. Weighted thresholds inherit the finite-profile boundary

Corollary 44.6 is likewise read over

$$
\mathcal C_K^{\mathrm{fin}},
$$

not over the larger class of merely source-total controllers. Its threshold
set is therefore

$$
\widetilde{\mathcal W}^{\mathrm{fin}}_{K,\lambda}
 =\{z\in\mathbb N:\exists C\in\mathcal C_K^{\mathrm{fin}},\;
                         M W_\lambda(C)\le z\}.
$$

The path certificate must include the same finite vector $x$ and uniform
source bound from Sections 47--49 before it decides this set. A controller
with $b(C)=(0,\infty)$ can have finite weighted cost for a weight that ignores
the unbounded coordinate, but it is not a witness for the finite-profile
threshold set. If unrestricted source-total weighted optimization is desired,
it is a separate problem requiring its own decision and attainment hypothesis;
it is not supplied by the finite Pareto theorem.
## 51. Redundant complete words with the original call trace

**Definition 51.1 (the supplied complete finite controller).** Let $Q$ be
all installed logical states of a controller, with $K=|Q|\ge1$. Include
halt states, unreachable states, error states and every installed invalid-code
completion. At $q\in Q$ there is one fixed original instruction $I(q)$:
either a primitive with its entire literal payload, or $\mathsf{Halt}(Y_q)$
with one fixed complete output. A nonhalt instruction has a declared finite
typed-response set $O_q$ and a total table

$$
\delta_q:O_q\longrightarrow Q.
\tag{FIB.51.1}
$$

Every typed response has its row, whether or not it is possible on an
admitted source. A silent primitive uses its declared constant response, such
as $\bot$ in Definition 46.1. A primitive that is undefined outside its
legal domain remains undefined there; this definition supplies no observable
failure response for a missing strict edge. Halt has no response rows.
For notational uniformity put $O_q=\varnothing$ at a halt, with its
unique empty successor map.

The source and apparatus domains may be infinite. Their original legality,
actual response and apparatus-successor maps are retained. The complete
proof-side apparatus state includes any history needed by these maps, as in
§47; it is not an additional observer input. All mutable information used
by instruction selection is already in $q$, and its next value depends only
on $q$ and the actual declared response. In particular, the all-action
factorization of Definition 46.1 is a premise. A source-indexed successor
list that fails this factorization is not an input controller.

Initialization is either a common $q_0$ or a map $c(i)\in Q$ of an initial
record $i$ that was genuinely acquired under the original contract. The
original source, target and acquired record stay paired. Neither an arbitrary
source label nor a retrospectively compatible history qualifies as $i$.
The record is not available again after initialization unless already
represented in the counted control.

Use exactly the conditional whole-word instruction and immediate-response
services of [FIB continuation II][FIB51-II], Definition 45.1. A word is the
whole mutable observer. The static instruction service selects the original
instruction; that primitive's transient response immediately selects hold or
one legal bit flip and is discarded. There is no intervening instruction.
These control services obtain no further source response and perform no
apparatus update beyond the declared original primitive.
Installation, acquisition, initialization, selection, literal delivery,
primitive execution, response writing and output are supplied and charged
separately. The premise grants these functions at the chosen finite width;
it does not construct their physical implementation from a word count.

**Theorem 51.2 (finite redundant realization of every typed row).** For
any controller in Definition 51.1, these conditional services admit a finite
installed set $W\subseteq L_\ell$ and a proof-side surjection
$\pi:W\to Q$ with fixed instruction table $\widehat I$ and immediate
response table $\widehat\delta$, satisfying

$$
\begin{aligned}
\widehat I(w)&=I(\pi(w)),\\
\pi(\widehat\delta(w,o))&=\delta_{\pi(w)}(o),\\
d_H(w,\widehat\delta(w,o))
 &=\mathbf1_{\{\delta_{\pi(w)}(o)\ne\pi(w)\}}
 \qquad(o\in O_{\pi(w)}).
\end{aligned}
\tag{FIB.51.2}
$$

For $K\ge2$, put

$$
r=\lceil\log_2K\rceil,\qquad m=2^r-1,\qquad
f=2^{m-r}.
\tag{FIB.51.3}
$$

One realization has

$$
\ell=2m-1=2^{r+1}-3,\qquad |W|=Kf,
\qquad |\pi^{-1}(q)|=f\quad(q\in Q).
\tag{FIB.51.4}
$$

For $K=1$ one may take $\ell=1$, $W=\{0\}$ and $f=1$.
These bounds depend on the installed controller, not on source cardinality,
a maximum execution length or an acyclicity assumption.

For each admitted source and its original initialization, the realization
preserves every original primitive, entire submitted literal, actual raw
response, apparatus successor and original target. A first Halt exists in
one run exactly when it exists in the other; its complete output and the
number of preceding primitives are equal.
This includes immediate halt, every finite execution prefix and infinite
runs. Legality, success and termination transfer wherever the original
controller has them; they are not conclusions about an arbitrary finite
table solely from its encoding.

Proof. For $K\ge2$, label the logical states injectively by
$a:Q\hookrightarrow\mathbb F_2^r$. Index the $m$ data coordinates in a
fixed order by the nonzero vectors $v\in\mathbb F_2^r$. Use the classical
Hamming check map and the zero-interleaving map

$$
\sigma(x)=\sum_{v\ne0}x_vv,\qquad
J(x_1,\ldots,x_m)=x_1\,0\,x_2\,0\,\cdots\,0\,x_m.
\tag{FIB.51.5}
$$

The all-distinct nonzero check vectors and the rule identifying a one-bit
change by its check vector are the Hamming construction in *Matrix Hamming
Codes*, §§9.1–9.3 [MIT-HAMMING]. The displayed zero-interleaving map is
Cabello–Eppstein–Klavžar's Proposition 3.1 [FIB51-CEK]. These are
literature-attested ingredients, not new coding or coloring results.
Their use here does not require the old controller graph to embed in a cube.

The check vectors include a basis, so $\sigma$ is onto. Fixing all $m-r$
coordinates outside those basis positions leaves a unique choice of the
basis coordinates for each prescribed syndrome. Each syndrome fiber
therefore has exactly $f$ elements. Install precisely

$$
W=\{J(x):\sigma(x)\in a(Q)\},\qquad
\pi(J(x))=a^{-1}(\sigma(x)).
\tag{FIB.51.6}
$$

Thus each logical state has exactly $f$ installed aliases, including states
with empty actual support. When $K<2^r$, the unused syndrome fibers are not
installed. Neither these words nor other ambient no-$11$ words have rows.
The map $J$ is injective, has length $2m-1$ and always gives a no-$11$ word.

At $w=J(x)$ install the exact instruction $I(q)$, where $q=\pi(w)$.
For each typed response $o$, put $q'=\delta_q(o)$ and $d=a(q)+a(q')$.
If $d=0$, install hold. Otherwise install the flip of data coordinate $d$,
namely physical bit $2\operatorname{index}(d)-1$. If $e_d$ is the unit
vector in that data coordinate, then

$$
\sigma(x+e_d)=\sigma(x)+d=a(q').
\tag{FIB.51.7}
$$

The successor is in $W$, projects to $q'$ and differs in one physical bit.
All separator bits stay zero. Injection of $a$ gives $d=0$ exactly when
$q=q'$, proving all three equations (FIB.51.2). This specifies every typed
row, including error transitions and responses with empty actual support;
none is replaced by a convenient hold unless the original successor is
$q$ itself. Every alias of a halt state has its original fixed full output
and no response entries.

For a common initial state, choose $a(q_0)=0$ and initialize at $0^\ell$.
More generally the explicit section

$$
s(q)=
\begin{cases}
J(0^m),&a(q)=0,\\
J(e_{a(q)}),&a(q)\ne0
\end{cases}
\quad\text{satisfies}\quad \pi(s(q))=q.
\tag{FIB.51.8}
$$

Initialize to $s(c(i))$ using only the genuinely acquired $i$. This is one
separately supplied whole-word initialization; it is not a response step
or a free acquisition of $i$. For $K=1$, the sole instruction is copied to
word $0$, every typed successor holds, and the same claims follow directly.

The quantities $a,\sigma,\pi,q,q'$ and $d$ in these formulas specify
finite static rows. They are not runtime computations or registers. Each
entire installed word already selects its fixed original instruction, and
each pair of that word and a typed response already selects hold or one
fixed bit index. The conditional service has no external decoded PC,
syndrome, phase, response latch or retained history. If an implementation
needs such persistent state to perform the selection, it does not satisfy
Definition 51.1's complete-word service premise.

For the execution proof, relate an old boundary $(z,s,q)$ to a new boundary
$(z,s,w)$ by $\pi(w)=q$, retaining the same original target $z$, complete
apparatus state $s$ and ordered primitive history. Initialization establishes
this relation. At related nonhalt boundaries, the instructions and their
legality domains are equal. The same primitive with the same literal acts
on the same apparatus, giving the same actual response and successor.
Equation (FIB.51.2) restores the relation immediately. No instruction occurs
between this response and the next corresponding boundary. Induction proves
equality of every finite original event prefix. If execution reaches an
undefined action, both sides have the same undefined action; no success or
failure sensor is manufactured there.

A new boundary is a halt exactly when its projected old boundary is one,
with exactly the same output. Hence finite first halt and zero-call first
halt correspond in both directions. An infinite original run has arbitrarily
long matching finite prefixes; the recursively defined new run cannot halt
at any finite boundary and is infinite. Conversely an infinite new run
projects to the infinite old run. A logical cycle may return to another
alias of its starting state; future rows still obey (FIB.51.2). No unfolding
of histories and no bound on the number of traversals was used. $\square$

## 52. Full installation bills and the transfer boundary

**Corollary 52.1 (aliases, payloads and one matched run).** Use Theorem
51.2, with its $f=1$ convention when $K=1$. Let $K_H$ count old halt states
and let $E_0=\sum_{q\text{ nonhalt}}|O_q|$. The realization has exactly

| Installed item | Count |
| --- | --- |
| Complete words and instruction rows | $Kf$ |
| Aliases of each individual logical state | $f$ |
| Halt rows, including unreachable halts | $K_Hf$ |
| Typed response entries | $E_0f$ |
| Full word-key bits in an explicit table | $Kf\ell$ |
| Hold/flip-index bits for the typed entries | $E_0f\lceil\log_2(\ell+1)\rceil$ |

If $\mathcal R$ is the set of old literal-Read states with literal $p_q$,
the new Read-row count is $f|\mathcal R|$. Its distinct installed literal
union is exactly the old one. Fully inlining the literals gives exactly
$f\sum_{q\in\mathcal R}|p_q|$ address letters, with $f$ copies of each
old row's payload. Empty literals have zero letters but still have rows,
length fields, delivery and execution. Each old fixed halt payload is
likewise installed $f$ times; no two different old halt states are silently
merged merely because their outputs coincide.

For a finite terminating run with logical states $q_0,\ldots,q_n$, the
native call count is exactly the original $n$. There are $n+1$ instruction
selections including Halt, $n$ immediate response selections and one output.
The response bit-change count is

$$
b=\sum_{j=0}^{n-1}\mathbf1_{\{q_{j+1}\ne q_j\}}\le n.
\tag{FIB.52.1}
$$

The same identity holds on every finite prefix of a nonterminating run.
Counts of each primitive, submitted literal order and address-length sums,
actual apparatus epochs and source-state peaks are preserved on the same
source whenever these coordinates are defined by the original events.
Initialization writes, table-selection costs and other implementation
services are not included in this equality of event coordinates.

Proof. Each old state has $f$ aliases, and each alias copies precisely that
state's instruction, payload and typed-response list. This gives the table
and payload counts. Equation (FIB.51.2) gives the exact bit-change indicator;
the execution correspondence gives the remaining same-run equalities.
No source maximum or coordinate minimum was taken. $\square$

**Definition 52.2 (an explicit finite table representation).** Suppose
the old fixed instructions, including their response types, literal lengths
and complete halt outputs, have supplied finite binary records. Let $b_I$
be a common padded record width, and fix the response order for each such
record. Put

$$
t_* =\max\bigl(\{0\}\cup\{|O_q|:q\text{ nonhalt}\}\bigr),\qquad
\beta=\lceil\log_2(\ell+1)\rceil.
$$

One explicit rectangular representation stores, for each of the $Kf$ words,
its full $\ell$-bit key, its $b_I$-bit instruction record and $t_*$ response
slots of $\beta$ bits each. Zero means hold; $j\in\{1,\ldots,\ell\}$
means flip physical bit $j$. Unused slots are fixed zero padding, not typed
response entries. Its exact record-array length is

$$
S_{\rm rows}=Kf(\ell+b_I+t_*\beta).
\tag{FIB.52.2}
$$

The supplied format, record interpretation and any extra framing, dictionary,
index or selection apparatus are charged in addition when present. The
literal and halt payloads already included in $b_I$ must not be charged
a second time as extra row-array bits. If output objects have no supplied
binary representation, Corollary 52.1 counts their copies but assigns no
finite bit-length to them by fiat.

A stored common initial word adds $\ell$ immutable bits. For acquired-input
initialization, an explicit section table for (FIB.51.8) instead adds
$K\ell$ word bits in the original fixed state order, plus its framing and
the original realization of $c(i)$. The acquisition and selection of $i$
and the physical initialization service retain their original permissions
and separate prices. Existence of this finite section does not realize an
arbitrary unsupplied map $c$ on an infinite input domain.

For a matched finite run, use the cost vector

$$
\begin{aligned}
C={}&C_{\rm acquire}+C_{\rm promise/source}
 +C_{\rm compile/install}+C_{\rm init}(i)\\
 &+\sum_{j=0}^{n-1}\bigl(
 C_{\rm select}(w_j)+C_{\rm deliver}(I(q_j))
 +C_{\rm primitive}(I(q_j),s_j)
 +C_{\rm response}(w_j,o_j)\bigr)\\
 &+C_{\rm select}(w_n)+C_{\rm output}(Y_{q_n}).
\end{aligned}
\tag{FIB.52.3}
$$

Terms charge the services actually supplied and do not assume zero tariffs.
Compilation and installation have finite combinatorial descriptions here;
their physical time, workspace and energy are not inferred from
(FIB.52.2). The trace equality does not identify new selection or output
tariffs with the old ones.

**Corollary 52.3 (inherited certificates and distinct realization scopes).**
Given the old exact reachable supports $C_q$, let $\widehat C_w$ be the
exact support at $w$ in the matched new runs. Then

$$
\widehat C_w\subseteq C_{\pi(w)},\qquad
\bigcup_{\pi(w)=q}\widehat C_w=C_q.
\tag{FIB.52.4}
$$

An existing support–rank certificate from continuation II, Theorem 27.2,
restricts to the new exact supports by
$\widehat\rho(z,s,w)=\rho(z,s,\pi(w))$. All its legality, closure,
descent and fixed-output conditions hold there. This is a reuse of that
certificate theorem; support closure alone supplies no rank or termination.
In particular, (FIB.52.4) does not assert that each alias has the whole old
exact support. Some aliases can remain unreachable.

Proof. Each actual new prefix projects to its old prefix, proving inclusion.
Every actual old prefix has its lifted prefix, proving the union equality.
The commuting successor equation and equal primitive supply the conditions
of the old certificate on each restricted support; any assumed strict rank
decrease is therefore retained. $\square$

The present realization has a surjective logical correspondence with $Kf$
installed states. It is distinct from continuation II's Theorem 45.4, which
requires one word per old state and is subject to the fixed $K_{2,3}$
obstruction of Proposition 46.2. It is also distinct from Corollary 47.2's
actual-history forest, whose bounds require finite sources and a finite
maximum actual length and which need not preserve unsupported typed rows.
Those results remain in their original scopes. This construction neither
reproves their graph statements nor supplies a compact optimum. When a
budget counts every installed state, the new witness belongs at budget
$Kf$, not $K$.

The all-action and complete-history requirements of §§41, 46–47 remain
premises. This realization does not synthesize an ExactChart, repair the
pseudo-controller of Counterexample 41.4, authenticate a source promise or
turn a cycling candidate cover into a successful controller. Nor does it
supply the uniform bounds or exact acceleration required by §§47–50 for
finite-profile decision and Pareto conclusions. An infinite-domain controller
may terminate on each source with unbounded worst event cost, and that
property is also preserved.

The Hamming check construction and zero interleaving in Theorem 51.2 are
literature-attested. The complete typed-table application, exact original
execution correspondence and itemized installation bill are repo-derived
ordinary conditional mathematics. No new Hamming code, syndrome method,
coupon coloring, graph classification, optimal width or total physical-cost
claim is made. These statements provide no Lean/kernel certification.

[MIT-HAMMING]: https://math.mit.edu/~djk/18.310/Lecture-Notes/matrix_hamming_codes_2007.html
[FIB51-CEK]: https://arxiv.org/pdf/0903.2507v1
[FIB51-II]: FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md

## 追加锚（本行以下为增补区）

## 53. Sharp installation bounds for saturated complete-successor controllers

**Definition 53.1 (the strict saturated comparison).** Fix a controller
of Definition 51.1 with $K=|Q|\ge2$, all states nonhalting, and
$O_q=Q$, $\delta_q(o)=o$ for every $q,o\in Q$. Each state retains its
fixed original instruction $I(q)$ and entire literal payload. Saturation
concerns the designated typed rows, not the actual support of their replies.
An installation consists of a nonempty finite set

$$
W\subseteq L_\ell
=\{w\in\{0,1\}^\ell:w_jw_{j+1}=0\ (1\le j<\ell)\},
\qquad \pi:W\twoheadrightarrow Q,\qquad M=|W|,
$$

where $\ell\ge1$ and $\pi$ is proof-side correspondence only. Every word
is the entire mutable observer. Its fixed instruction is $I(\pi(w))$.
A valid fixed static response table is a function
$R:W\times Q\to W$ satisfying, at every installed word and every typed reply,

$$
\pi(R(w,o))=o,\qquad d_H(w,R(w,o))\le1.
\tag{FIB.53.1}
$$

Unsupported replies and unreachable installed words are included. The
conditional services are exactly those of Definition 51.1 and continuation
II, Definition 45.1: the original primitive's transient reply selects hold
or one legal bit flip immediately and is discarded, without an intervening
instruction, further source observation or extra apparatus update. No decoded
label, PC, syndrome, latch, stage or retained record exists outside the word.
Initialization uses either the same actual common $q_0$ or the same genuinely
acquired record $i$ and its original $c(i)$, paired with the same source and
target; choose a word over that state. Such whole-word initialization is a
separately supplied service, not an acquisition of $i$ or later access to it.
The original source legality and all-action factorization remain premises.
Acquisition, source promises, installation, initialization, selection, literal
delivery, primitive execution and response writing retain their separate
charges from §§51–52. No count here supplies these services physically.

Write $G_W$ for the induced Hamming-distance-one graph on $W$, and put
$N_W[w]=\{u\in W:d_H(u,w)\le1\}$. All neighborhoods below are installed
neighborhoods, including their centers.

**Proposition 53.2 (exact static-table existence).** For fixed $W$ and
$\pi$ in Definition 53.1, a valid response table exists if and only if

$$
\pi(N_W[w])=Q\qquad\text{for every }w\in W.
\tag{FIB.53.2}
$$

Proof. A valid table supplies $R(w,o)\in N_W[w]\cap\pi^{-1}(o)$ for
each $o$, proving necessity. Conversely, fix an order on the finite set
$W$. For each pair $(w,o)$ choose the first member of this nonempty
intersection, choosing $w$ itself when $o=\pi(w)$. These choices give one
fixed table satisfying (FIB.53.1), with hold on the same label and one flip
on every different label. Coverage proves existence; a preselected table
must still satisfy (FIB.53.1) row by row. In particular, coverage alone
does not certify an arbitrary assignment of successors. $\square$

Condition (FIB.53.2) says that the label classes form a domatic partition
of $G_W$: each is a dominating set in the closed-neighborhood sense of
Zelinka, *Domatic numbers of cube graphs*, pp. 117–119 [FIB53-ZELINKA].
It does not require every label in the open neighborhood; the center supplies
its own label.

**Theorem 53.3 (installation bounds and equality rigidity).** Every valid
installation of Definition 53.1 satisfies

$$
\ell\ge2K-3,\qquad M\ge2^{K-1}.
\tag{FIB.53.3}
$$

Put $d=K-1$. If $\ell=2d-1$, the installed set is exactly the odd-coordinate
cube

$$
W=\{x_1\,0\,x_2\,0\,\cdots\,0\,x_d:x\in\{0,1\}^d\}.
\tag{FIB.53.4}
$$

If $M=2^d$, then $W$ is a coordinate $d$-cube in $\{0,1\}^\ell$:
exactly $d$ coordinates vary independently and all others are fixed padding.
The whole face must lie in $L_\ell$. Thus its free positions are pairwise
nonadjacent, fixed positions adjacent to them are zero, and the remaining
fixed bits obey the no-$11$ constraint.

Proof. Proposition 53.2 gives $|N_W[w]|\ge K$, hence every vertex has
degree at least $d$. Choose an installed word of maximum Hamming weight.
Every installed neighbor decreases its weight, so its degree is at most
its weight, which is at most $\lceil\ell/2\rceil$ for a no-$11$ word.
Consequently $d\le\lceil\ell/2\rceil$ and $\ell\ge2d-1$.

Suppose $\ell=2d-1$. The only no-$11$ word of weight $d$ has ones in
positions $1,3,\ldots,2d-1$: fitting $d$ ones with a gap between each pair
uses all $2d-1$ positions. Every word with an even-position one therefore
has weight at most $d-1$. If any such word is installed, choose one of
maximum weight among that subset. An upward installed neighbor would still
have its even-position one and contradict maximality in the subset.
Its degree is therefore at most $d-1$, a contradiction. Hence $W$ lies in
the odd-coordinate $d$-cube. Degree at least $d$ now forces all $d$ cube
neighbors of each installed word to be installed. Nonemptiness and the
connectivity of the cube force all its vertices, proving (FIB.53.4).

For the size bound, Simon's cube lemma is supplied by Ambainis–Vihrovs,
*Size of Sets with Small Sensitivity: a Generalization of Simon's Lemma*,
§3, Theorem 1 and Corollary 1, pp. 4–5 [FIB53-AV]. For the actual minimum
degree $D$ it gives $M\ge2^D$, with equality only for a coordinate
$D$-cube. There is no irreducibility premise in this result. Here $D\ge d$,
so $M\ge2^D\ge2^d$; equality $M=2^d$ forces $D=d$ and a coordinate
$d$-cube, with the stated padding restrictions imposed by $W\subseteq L_\ell$.

For a direct proof of this classical step, induct on ambient dimension.
For a nonempty induced cube subgraph of minimum degree at least $t$,
the case $t=0$ has size at least one, with equality a singleton.
For $t\ge1$, a constant coordinate
can be deleted and induction applied unchanged. Otherwise split a varying
coordinate into its two nonempty slices. Each slice loses at most one
neighbor per vertex, so has minimum degree at least $t-1$ and, by
induction, at least $2^{t-1}$ vertices. Equality in the summed bound
forces both slices to be coordinate $(t-1)$-faces. Their internal degrees
are exactly $t-1$, so every vertex must have its cross-slice mate. Their
projections coincide, and adjoining the split coordinate gives a coordinate
$t$-face. This proves both the bound and its equality assertion. $\square$

**Corollary 53.4 (perfect label classes at either equality).** If either
$\ell=2K-3$ or $M=2^{K-1}$ holds in a valid installation, then every label
class $C_q=\pi^{-1}(q)$ is a perfect radius-one code inside the installed
$(K-1)$-cube, and

$$
K|C_q|=2^{K-1},\qquad K\mid2^{K-1}.
\tag{FIB.53.5}
$$

In particular $K$ is a power of two. Equality in the width bound also
forces equality in the size bound; equality in size permits fixed padding.

Proof. Theorem 53.3 makes $W$ a $d$-cube in either case. Each closed
neighborhood has $d+1=K$ vertices and all $K$ labels, each exactly once.
For each fixed $q$, every vertex of this cube is therefore within distance
one of exactly one member of $C_q$. The radius-one balls centered at
$C_q$ partition the installed cube and each contain $K$ vertices. Counting
gives (FIB.53.5). Every prime divisor of $K$ must divide a power of two,
so $K=2^r$ for an integer $r\ge1$. This is the domatic fullness/divisibility
argument used for ordinary cubes by Zelinka, p. 117 [FIB53-ZELINKA], applied
after the installation rigidity has been established. These are balls in
$G_W$, not balls required to partition the whole Fibonacci graph
$\Gamma_\ell$. The argument does not classify the labellings or require
them to be linear. $\square$

**Proposition 53.5 (degree alone is insufficient).** For $K=3$, the
zero-interleaved square $W=\{000,001,100,101\}\subseteq L_3$ has minimum
degree $2=K-1$ but admits no three-label closed-neighborhood coverage.

Proof. Each closed neighborhood has three vertices. Coverage would put
each label there exactly once. Counting occurrences of one fixed label
over all four closed neighborhoods gives $3|C_q|=4$, since every vertex
belongs to three such neighborhoods. This contradicts $3\nmid4$.
Thus the degree consequence of Proposition 53.2 cannot replace its full
coverage condition. $\square$

**Theorem 53.6 (one common least pair and its universal boundary).** Fix
the original controller, source contract and initialization of Definition
53.1. Order installation pairs by
$(\ell,M)\preceq(\ell',M')$ when $\ell\le\ell'$ and $M\le M'$.
If $K=2^r$ with $r\ge1$, the attainable pairs have the common least element

$$
(\ell_*,M_*)=(2K-3,\,2^{K-1}).
\tag{FIB.53.6}
$$

If $K$ is not a power of two, every valid installation instead satisfies
$\ell\ge2K-2$ and $M>2^{K-1}$. A finite attainable upper pair remains

$$
r=\lceil\log_2K\rceil,\quad m=2^r-1,\qquad
(\ell,M)=(2m-1,\,K\,2^{m-r}).
\tag{FIB.53.7}
$$

Proof. Reuse the single installation of Theorem 51.2 on this same original
controller. When $K=2^r$, its state labelling exhausts all syndromes, so
(FIB.51.6) installs the entire zero-interleaved $m$-cube, with $m=K-1$.
Its already specified typed response table obeys (FIB.53.1), and
$K2^{m-r}=2^m=2^{K-1}$ while $2m-1=2K-3$. This one witness attains both
bounds of Theorem 53.3 and is below every competing pair in the product
order. For $K=2$ it is simply $W=\{0,1\}$ at width one. Initialization is
the section (FIB.51.8) on the same actual common state or acquired record;
its supplied service and charges remain in force. No separate coordinate
minimizers or different-source runs have been combined. For nonpowers,
Corollary 53.4 excludes either equality, and integrality gives the stated
strict bounds. Theorem 51.2 with its unused syndrome fibers omitted gives
(FIB.53.7). These arguments leave the exact minima for nonpowers unsettled.
$\square$

The attaining witness uses the classical Hamming check construction of
*Matrix Hamming Codes*, §§9.1–9.3 [MIT-HAMMING], and the zero interleaving
of Cabello–Eppstein–Klavžar, Proposition 3.1, p. 5 [FIB51-CEK], through
Theorem 51.2. Simon's size/equality result, the domatic argument and these
upper-bound ingredients are literature-attested. The saturated controller
application, no-$11$ width rigidity and common-pair conclusion are
repo-derived ordinary conditional mathematics, with no global novelty claim.

At powers of two this is also a sharp universal-compiler worst-case pair:
Theorem 51.2 supplies it for every $K$-state controller under its own
state-corresponding all-row contract, while the saturated nonhalting subclass
forces both coordinates. It is not a pointwise lower bound for every
$K$-state table. For example, a nonhalting table whose every reply returns
to its current state can use $K$ distinct unit words of length $K$, one per
state, with every response holding. For $K\ge3$ its $M=K<2^{K-1}$.

The lower-bound comparison excludes halts, supported-only or reachable-only
row obligations, sparse parity controllers such as SLHC §13, and arbitrary
trace-only implementations without the stipulated surjection. Nonhalting
does not prove an action legal or a run infinite: an undefined original
primitive stays undefined. The pair counts width and installed words only;
it asserts no optimum for latency, energy, total cost or service availability,
no uniqueness of a labelled optimum, no classification of perfect codes in
the whole Fibonacci graph, and no termination, finite-profile or execution
Pareto conclusion. Those claims require their separate original premises.

[FIB53-AV]: https://eccc.weizmann.ac.il/report/2014/077/revision/2/download
[FIB53-ZELINKA]: https://dml.cz/bitstream/handle/10338.dmlcz/129735/MathSlov_32-1982-2_2.pdf

## 追加锚（本行以下为增补区）

## 54. The K=3 common least pair under strict saturation

**Theorem 54.1 (the saturated three-state frontier).** Keep Definition 53.1
unchanged, including all installed words, all typed replies, unsupported rows,
unreachable rows, the onto map, the complete original instruction and literal
at every word, and the immediate hold-or-one-bit response rule. For $K=3$ the
coordinatewise common least attainable pair is

$$
(\ell_*,M_*)=(4,6).
\tag{FIB.54.1}
$$

The lower statements already proved in §§53.3--53.6 give
$\ell\ge4$, $M\ge5$, and the attainable upper pair $(5,6)$. It remains to
exclude $M=5$ and to exhibit one width-four table.

**Five-word obstruction.** Let $G_W$ be the induced Hamming graph of a
hypothetical valid $W$ with $|W|=5$. Proposition 53.2 is used first, not
replaced: every closed installed neighborhood contains all three labels, so
$|N_W[w]|\ge3$ and every vertex of $G_W$ has degree at least two. The graph is
bipartite, since Hamming-one edges change word parity. Every component of a
finite bipartite graph of minimum degree two contains a cycle of length at least
four; with five vertices this forces one connected component. Neither bipartition side can have size one, because vertices on the other
side would then have degree at most one. Its bipartition therefore has parts
of sizes two and three. The three-vertex side contributes at least
six incident edges, while at most $2\cdot3=6$ bipartite edges are possible.
Thus $G_W$ would have to be $K_{2,3}$.

This cannot be an induced subgraph of a Boolean cube. Two distinct cube
vertices that have a common neighbor differ in exactly two coordinates, and
then they have exactly two common neighbors (flip either differing coordinate).
The two vertices in the size-two side of $K_{2,3}$ would have three common
neighbors. Hence no valid installation has five words, and therefore
$M\ge6$. The closed-neighborhood hypothesis is essential: degree two by
itself does not provide the three labels, as Proposition 53.5 already shows
for its four-word square.

**Width-four witness.** Put

$$
W=\{0000,0001,0100,0101,1000,1001\}\subset L_4,
$$

and define the onto correspondence

$$
\pi(0000)=\pi(0001)=0,\qquad
\pi(0100)=\pi(1001)=1,\qquad
\pi(0101)=\pi(1000)=2.
$$

The following is one fixed table; the three response columns are in the order
$o=0,1,2$.

| $w$ | $\pi(w)$ | $N_W[w]$ | $R(w,0)$ | $R(w,1)$ | $R(w,2)$ |
|---|---:|---|---|---|---|
| $0000$ | 0 | $\{0000,0001,0100,1000\}$ | $0000$ | $0100$ | $1000$ |
| $0001$ | 0 | $\{0000,0001,0101,1001\}$ | $0001$ | $1001$ | $0101$ |
| $0100$ | 1 | $\{0000,0100,0101\}$ | $0000$ | $0100$ | $0101$ |
| $0101$ | 2 | $\{0001,0100,0101\}$ | $0001$ | $0100$ | $0101$ |
| $1000$ | 2 | $\{0000,1000,1001\}$ | $0000$ | $1001$ | $1000$ |
| $1001$ | 1 | $\{0001,1000,1001\}$ | $0001$ | $1001$ | $1000$ |

Every displayed word has no adjacent ones. Each response is the center or a
Hamming-one neighbor, and its image under $\pi$ is exactly $o$. Each displayed
closed neighborhood contains all of $\{0,1,2\}$, so Proposition 53.2 certifies
all eighteen typed rows, including rows with no actual support. At each word
install the original instruction $I(\pi(w))$ with its entire literal payload.
For a common initial state, choose one of $0000,0100,0101$ according to its
label; for an acquired $c(i)$ choose the corresponding listed word, using only
the original acquisition. Thus the original
source/target pairing, all-action factorization, undefined-action boundary,
and same-source event-prefix correspondence from §§46 and 51 remain intact.
No decoded label, PC, syndrome, phase, latch, controller field, or retained
record is added outside the whole word.

The lower bounds and this witness prove (FIB.54.1) in the product order. The
classical suppliers used by the preceding bounds are Simon's cube lemma and
gap theorem (Ambainis--Vihrovs, ECCC 2014/077 revision 2, Theorem 1,
Corollary 1 and Theorem 3, pp. 4--5) and the closed-neighborhood/domatic
formulation (Zelinka, *Domatic numbers of cube graphs*, pp. 117--119), as
already cited in §§53.3--53.4. The five-word obstruction and the table above
are the present controller application; they add no coding, graph-classification,
or optimizer theorem. CEK Proposition 3.1 and the MIT Matrix Hamming §§9.1--9.3
supply the existing $(5,6)$ construction in §51; they are not needed to
justify the new width-four witness.

A bounded fresh-source comparison at dev pin
$d2488e18542d1070abf4b7173900b88ecc32112f$ covers distinct
stationary-law, serial-paid-local, and sparse/halting contracts, with no matching
Definition 53.1 saturated $K=3$ frontier. This is overlap evidence within the
checked sources, not an exhaustive corpus or novelty claim. The IV file at that
pin lacks §§51--53; this records absence at that pin and does not assert that
unmerged IV text was deleted. Initialization, acquisition, source promises,
installation, selection, literal delivery, primitive execution, response
writing, and output remain separately supplied and charged. No physical-service,
termination, latency, total-cost, or kernel-validation conclusion follows.

## 55. Mathematical citation for the sparse parity example in §53

**Citation convention (for §53).** The phrase “sparse parity controllers
such as SLHC §13” in §53 designates [SLHC §14, Theorem 14.2 and
Corollary 14.3][FIB55-SLHC]: the redundant realization of the entire
Construction 11.5 table, with fixed halts and the original call trace.
SLHC §13, “Bounded genuine Updates and binary-size native acquisition”,
has a different clock-cell construction; it is not the construction
designated by this particular citation.

[FIB55-SLHC]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT_CONTINUATION.md#14-unknown-shape-parity-with-no-added-routing-calls

## 追加锚（本行以下为增补区）
