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
