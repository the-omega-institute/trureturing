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
