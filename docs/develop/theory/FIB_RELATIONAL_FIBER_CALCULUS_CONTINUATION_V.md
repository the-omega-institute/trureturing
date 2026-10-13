# FIB Relational Fiber Calculus · Continuation V
## —Action-closed quotients, task controllers, and source-uniform kernels

> **Machine contract.** This is a `generic-v1` theory reference volume. The
> definitions and results below are ordinary mathematical prose, not Lean
> declarations. They make no kernel-verification claim. The volume is an
> append-only source and ends with an append anchor.

**来源。** AI-authored theory by a Codex implementation worker. This volume
is a repository-derived mathematical exposition, with prior methods cited
below; it is not user-provided original theory. It is a pure theory reference
and makes no Lean/kernel-verification claim.

[FIB Relational Fiber Calculus · Continuation IV](FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_IV.md)
supplies an executable ExactChart boundary and a conditional resource
feasibility contract, read with its published §§46--50 corrections. Its
historical §44.2 mixed-budget wording is superseded there by finite-profile
feasibility, uniform source-total history certificates, and the corresponding
weighted-threshold restriction. Sections 58.18--58.21 reuse this corrected
interface; §58.20 gives one explicit sufficient finite-family implementation.
The next distinction is between
two different minimization problems. A quotient that predicts every allowed
future action is canonical;
a controller minimized for one target may choose one of several incompatible
strategies and therefore need not have a unique coarsest quotient.

[FIB Atom Recursive Holographic Boundary Geometry · Continuation IV, §107](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md#107-root-readout-action-closure-and-future-memory)
gives a finite-dimensional linear boundary for intervention words followed
by passive evolution and readout, in the order $C_\ell A^jT_w$. It does not
cover arbitrary interleavings of passive evolution and intervention;
[Relational II, §§44.5--44.7](FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md#44-固定原生菜单的边界因子化与交错动作修正)
supplies the mixed action-word contract used for that purpose here.
Neither linear contract transports resource tails. This volume first treats
deterministic finite contracts, then states a source-uniform record-law
extension under additional measurability and field-factorization assumptions.
Section 59 uses the source-specific signed occurrence states and fixed-time
root-readout gap of Holographic IV §110, with the exact old root-neighbor
residual of its (109.9), to derive an $O(n/N_n)$ old-curve separation bound
and a necessary noise and absolute-precision boundary for predicting that
comparison future. Its risk for full adversarial report balls on the two
preparations is determined exactly; neither exponent optimality nor a native
recovery procedure is supplied.

## 51. Complete action systems

**Definition 51.1 (boundary state and action response).** Let $Q$ be a set of
complete reachable boundary states. A state contains the controller position,
all epoch and ordered-history information needed by later actions, the hidden
physical state, and the current target row. Let $A$ be a set of primitive
non-halt actions and let $O_\bot$ be a visible response alphabet containing
$\bot$ for silent actions.

For $q\in Q$ and $a\in A$, write

$$
\operatorname{Leg}(q,a)\in\{0,1\},
\qquad
\operatorname{Resp}(q,a)\in O_\bot,
\qquad
\operatorname{Next}(q,a)\in Q,
$$

and let $\operatorname{cost}(q,a)$ be a resource vector. A halt state carries
a complete target row. A controller can observe the response but cannot read
an arbitrary coordinate of $q$.

**Definition 51.2 (action-labelled future).** For a state $q$, define its
finite labelled future language $L(q)$ recursively by all legal words whose
successive responses, terminal row, and accumulated resource labels are
obtained from the same state $q$. A word that reaches a halt is terminal; a
nonterminal word may be extended only when the next action is legal.

The full future includes silent actions as events. Therefore two states with
the same response phase count can still have different future languages because
one may admit a silent loop or a different resource trace.

**Definition 51.3 (universal action congruence).** An equivalence relation $R$
on $Q$ is an action congruence when, for every $qRq'$ and every $a\in A$,

$$
\begin{aligned}
\operatorname{Leg}(q,a)&=\operatorname{Leg}(q',a),\\
\operatorname{Resp}(q,a)&=\operatorname{Resp}(q',a),\\
\operatorname{cost}(q,a)&=\operatorname{cost}(q',a),\\
\operatorname{Next}(q,a)&R\operatorname{Next}(q',a),
\end{aligned}
$$

whenever the action is legal. Halt rows must also be equal on equivalent
states. If only a resource bound is relevant, the cost equality may be replaced
by equality of the contracted cost label declared by that contract.

This relation preserves all allowed behaviour. It is stronger than merely
preserving the target value or the existence of one successful protocol.

## 52. The greatest safe behaviour quotient

**Definition 52.1 (one-step completion operator).** For an equivalence relation
$R$ on $Q$, define

$$
q\,\Psi(R)\,q'
$$

when halt rows agree and every action has equal legality, equal visible
response, equal contracted cost, and $R$-equivalent legal successors. The
operator is understood on the lattice of equivalence relations ordered by
inclusion.

**Theorem 52.2 (greatest action-closed quotient).** The operator $\Psi$ is
monotone. Its greatest fixed point

$$
R_\infty=\nu\Psi
$$

is the largest action congruence. The quotient $Q/R_\infty$ is the coarsest
state representation that preserves every allowed finite future language,
terminal row, and contracted resource trace.

**Proof.** If $R\subseteq R'$, every $R$-equivalent successor pair is also
$R'$-equivalent, so $\Psi(R)\subseteq\Psi(R')$. Knaster--Tarski gives the
greatest fixed point of this monotone operator. On a finite state space it is
also obtained by the descending iteration $R_0=Q\times Q$,
$R_{n+1}=\Psi(R_n)$; every action congruence is contained in every $R_n$ and
therefore in the stable intersection. The fixed point is an equivalence
relation satisfying the four action clauses. Equality of one-step labels plus
induction on word length gives equality of every finite future trace.
Conversely, a difference in legality, response, cost, successor class, or halt
row supplies a one-step distinguishing context, so no larger safe quotient can
identify that pair. ∎

**Definition 52.3 (finite-depth approximants).** Put $R_0=Q\times Q$ and
$R_{n+1}=\Psi(R_n)$. On a finite state space, the descending chain stabilizes
at some $R_N=R_{N+1}=R_\infty$. In an infinite state space, the intersection
of all $R_n$ is the finite-trace action equivalence; equality with a quotient
for infinite histories requires an additional compactness or regularity
hypothesis.

**Corollary 52.4 (static summaries are safe exactly when action-closed).** A
summary map $\eta:Q\to M$ is a sound universal behavior quotient exactly when

$$
\eta(q)=\eta(q')
\Longrightarrow q\,R_\infty\,q'.
$$

A summary that preserves only the current readout is safe only if the readout
fibers are already action-closed. This is the action-closed future-memory
boundary made explicit in
[FIB Atom Recursive Holographic Boundary Geometry · Continuation IV, §107](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md#107-root-readout-action-closure-and-future-memory):
a static quotient can lose a response after an intervention word followed
by passive evolution. Its signature $C_\ell A^jT_w$ has that prescribed
order. For arbitrary mixed words, including passive evolution before an
intervention, use
[Relational II, §§44.5--44.7](FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md#44-固定原生菜单的边界因子化与交错动作修正).
These linear results supply no resource or record-law transport assumption;
§58.3 gives the precise executable-summary criterion used here.

## 53. Task-relative controller quotients

**Definition 53.1 (target and successful policy).** Let $g:Q\to Z$ be the
original target row and let a deterministic policy choose a legal action from
each nonterminal controller state as a function of its visible history. The
policy is successful when every admitted source reaches a halt with output
$g(q_0)$.

The policy induces a reachable controller graph $K_\pi$. Its states include
the policy program counter and every memory value used to choose the next
action; hidden source coordinates are not controller inputs.

**Definition 53.2 (policy-relative future equivalence).** For a fixed
successful policy $\pi$, two reachable controller states $k,k'$ are equivalent
when, under every admitted source compatible with that state, they have the same
remaining output on every visible response continuation and the same contracted
resource trace. The action selected at the two states is part of this future
contract.

**Theorem 53.3 (minimal controller for a fixed policy).** If $K_\pi$ is finite
and deterministic, quotienting it by policy-relative future equivalence yields
a successful controller with the fewest states among controllers implementing
the same visible response/output behaviour. Any two distinct quotient classes
are separated by a finite visible continuation or by a different selected
action, so no further merge preserves that behaviour.

**Proof.** Future-equivalent states have identical selected action and equal
response-indexed successors, so merging them is well-defined and preserves
all runs and outputs. If two states are not equivalent, a finite continuation
or the selected-action label distinguishes them; a controller identifying them
would produce the same instruction on that continuation and fail to preserve
the specified behaviour. Thus every implementation has at least one state per
class, and the quotient attains the lower bound. ∎

**Theorem 53.4 (task minimization is not a universal quotient).** Even when
every individual history is solvable within the same budget, the union of two
history fibres may require a different first action and become unsolvable. Thus
minimizing over successful policies is a two-stage problem:

$$
\min_{\pi\ \text{successful}}|K_\pi|,
$$

followed by minimization within the chosen policy. There need not be a single
coarsest partition that is simultaneously optimal for all successful policies.

**Proof.** Use the three calibration histories from Continuation II: each pair
has a common one-step experiment, but all three together have no common safe
first experiment. The partitions $\{1,2\}|\{3\}$ and
$\{1,3\}|\{2\}$ are both feasible, while their common coarsening is not. A
universal action congruence retains the distinctions required by every action;
a task quotient may retain only those required by one selected policy. ∎

## 54. Resources and quotient compatibility

**Definition 54.1 (resource-aware congruence).** Fix a resource contract
$\Gamma$. A relation is $\Gamma$-compatible when its action labels agree under
$\Gamma$ and its successor relation preserves the same source-indexed cost
composition. For additive costs, the trace cost satisfies

$$
C(q,aw)=\operatorname{cost}(q,a)+C(\operatorname{Next}(q,a),w).
$$

For maximum, cumulative, or weighted sourcewise resources, the aggregation
operator must be part of $\Gamma$; coordinatewise maxima from different
sources cannot be substituted for one same-source trace.

**Theorem 54.2 (quotient preserves a declared resource objective).** If $R$
is a $\Gamma$-compatible action congruence, every finite policy trace and its
contracted resource value are invariant under replacing a state by its
$R$-class. Consequently, finite-budget feasibility and fixed-policy resource
thresholds are preserved by the quotient.

**Proof.** Induct on the trace length. The first action has equal legality,
visible response and contracted cost in equivalent states, and the successor
states remain equivalent. Apply the induction hypothesis to the suffix. The
same argument applies to a finite response tree by induction on its height. ∎

A quotient may reduce the controller search space without reducing the actual
cost of interpreting or storing the quotient. Encoding cost and semantic action
cost remain separate resources.

## 55. Source-uniform randomized kernels

**Definition 55.1 (common-seed acquisition kernel).** Let $(U,\mathcal U,\mu)$
be one seed probability space. A source-uniform acquisition, after fixing
$u\in U$, applies one deterministic visible-response rule to every source.
The seed space, action rule, and response history semantics are common.
Measurability of each compared record and its termination event is an
additional assumption, as specified in §58.12; source-dependent resource
fields require their own measurable definitions.

For a source $s$, write $K_s$ for the finite-record law under §58.12's
almost-sure termination assumption, or for its finite-termination subprobability
law when divergence is permitted. The record includes nonhandoff branches and
the ordered requested addresses; it is not replaced by a mixture over sources.

**Theorem 55.2 (conditional uniform-kernel transport).** Under §58.12's
record-law contract, let $E$ be a measurable seed event on which two sources
terminate finitely under the same
common rule, with matched complete visible histories and stopping/status
information. If every compared record field is the same measurable function
of the seed and that history, the compared records agree almost everywhere
on $E$. Their event-restricted pushforward is dominated by both record laws
and hence by their abstract meet. This does not assert that the meet is
attained by an agreement event in the specified seed coupling.

**Proof.** The common seed and matched visible prefixes give the same
instructions and visible-memory updates. The matched stopping information
and stipulated field factorizations give the compared record equality.
Restriction to $E$ gives domination by both laws. The meet and its
event-attainment limitation are established in §§58.14--58.15. ∎

This is the stochastic counterpart of same-source event preservation. It does
not say that all sourcewise optimal resource tails are jointly attainable; the
common seed and one rule are the joint-realizability condition.

**Corollary 55.3 (deterministic and stochastic boundaries).** A deterministic
finite controller that terminates on every source is the degenerate case in
which $U$ is a singleton and every $K_s$ is a point mass. With the additional
record assumptions of §58.12, the common-seed layer and the finite
deterministic ExactChart layer have the same source-uniform execution
invariant, while their resource objectives and termination assumptions remain
separate contracts.

## 56. The three-layer controller theorem

**Theorem 56.1 (quotient, acquisition, and implementation).** Under a finite
source-total ExactChart contract with a declared resource objective:

1. $R_\infty$ is the greatest action-closed quotient preserving all allowed
   behaviour;
2. a successful policy on the quotient lifts to a successful policy on the
   original contract when all-action factorization and same-source updates hold;
3. a fixed lifted policy has a minimal finite controller given by its
   policy-relative future quotient;
4. finite profile bounds and a uniform horizon or exact acceleration are still
   required for finite resource decidability.

**Proof.** Item 1 is Theorem 52.2. Item 2 follows by induction on visible
responses because equivalent states have equal legality, response labels and
successor classes. Item 3 is Theorem 53.3. Item 4 is the finite-profile and
source-total correction from Continuation IV, and is independent of the
quotient construction. ∎

The order of operations is therefore forced:

$$
\boxed{
\text{build action-closed quotient}
\longrightarrow
\text{solve target acquisition}
\longrightarrow
\text{minimize selected controller}
\longrightarrow
\text{verify finite resources}.
}
$$

Reversing the order can merge histories that share a target but require
incompatible actions, or can report a finite resource value for an unbounded
source profile.

## 57. Boundary of the current result

The finite deterministic quotient theorems above are ordinary mathematics
under their stated contracts. They do not construct an action-closed quotient
for every signed FIB fibre, decide arbitrary measurable kernel optimization, or
identify physical time with event count. They also do not provide a unique
minimum controller across incompatible successful policies.

The next unresolved construction is an effective action-closed quotient for a
general signed FIB fibre that simultaneously preserves source ancestry,
all-action legality, terminal rows, and the selected resource objective. That
construction remains open.

**文献表态。** The coinductive greatest-fixed-point pattern and deterministic
future-language minimization are standard mathematical methods. The
source-uniform kernel formulation and its connection to the FIB boundary are a
repo-derived synthesis; no priority claim is made.

## 追加锚（本行以下为增补区）

## 58. Corrected contracts for executable quotients and common-seed transport

**Convention 58.1 (superseded clauses).** Sections 51--57 are read subject
to the following contracts. The current contract replaces the untagged one-step interpretation
of §§52.1--52.3 and the executable-quotient criterion of §52.4 by
58.2--58.3; the residual comparison and minimality claims of §§53.2--53.3 by
58.4--58.6; and the two-history wording of §53.4 and the missing policy-finiteness
conditions in §56.1 by 58.7--58.8 and 58.11. The resource assertions of §54 are
conditional on 58.9--58.10. The conditional record-law statements in
55.1--55.3 use the explicit record assumptions and meet limitations
in 58.12--58.15.
The historical effective-frontier wording of
[FIB Relational Fiber Calculus · Continuation IV, §44.2](FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_IV.md#44-conditional-resource-feasibility-and-its-pareto-basis)
is superseded by that volume's §§46--50. Its effective predicate is the
finite-profile alias of §49, subject to §§47--48's uniform boundedness and
source-total history requirements. Sections 58.18--58.21 distinguish this
predicate from the historical ordinary mixed test and give an explicit
sufficient implementation, without replacing the published repair.
Section 56.1 and its assertion of a forced order
are replaced by the conditional workflow in 58.16. The introductory references
to stochastic results and §55.3 are comparisons of mathematical settings, not attributions
of these statements to an exact Lean declaration; 58.17 gives their scope.

**Definition 58.2 (tagged universal action system).** On the complete state
space $Q$, distinguish the status
$\sigma(q)\in\{\mathsf{pending},\mathsf{halt},\mathsf{deadlock}\}$.
A halt has a complete terminal row $Y(q)$; a deadlock is a non-halt boundary
with no legal progress action. Neither is a pending state, even when no
response has yet been observed. Use a distinguished absent value for the
terminal row at every non-halt. For each primitive action $a$, record its
legality and definedness, and, when it is legal and defined, its visible
response (including an explicit silent-response symbol), contracted resource
label, and successor. Illegal and undefined cases have distinct tags and
absent response/cost/successor fields, rather than arbitrary values of those
fields. A legal-but-undefined case is a contract failure, not a successful
execution. Halts and deadlocks have no legal progress successor.

Let $t(q)=(\sigma(q),Y_\bot(q))$ and let $\ell_a(q)$ be the full
non-successor action-label tuple: legality, definedness, visible response
(including the silent-response symbol), contracted resource label, and the
distinct illegal, undefined, or other failure tag, with absent fields given
distinguished absent values. For an equivalence relation $R$, define

$$
q\,\Psi_{\mathrm c}(R)\,q'
\quad\Longleftrightarrow\quad
t(q)=t(q'),\quad
\ell_a(q)=\ell_a(q')\ \text{for every }a,\quad
\operatorname{Next}(q,a)\,R\,\operatorname{Next}(q',a)
\ \text{whenever }a\text{ is legal and defined}.
$$

Thus the empty continuation already observes pending versus halt versus
deadlock. An action congruence is an equivalence satisfying these root and
action labels and the successor clause. The monotone operator
$\Psi_{\mathrm c}$ maps equivalences to equivalences: for fixed $R$, its
comparison is equality of root labels, action labels, and legal successor
$R$-classes. Its greatest fixed point, here denoted $R_\infty$, is the
greatest such congruence. The usual fixed-point argument in §52.2 applies to
this tagged operator. Induction on finite words preserves every declared
label, including terminal status and contracted resources. Conversely,
equality of the complete finite labelled futures is itself an action
congruence, by taking a one-action derivative. This is the corrected finite
predictive contract; it makes no claim about infinite-trace realization.

**Proposition 58.3 (predictive safety versus an executable summary).** Let
$\eta:Q\to M$ and use only its image as the summary space. The condition

$$
\ker(\eta)\subseteq R_\infty
$$

means that equal summaries predict equal complete finite labelled futures.
It also gives a well-defined map
$\eta(Q)\to Q/R_\infty$, $\eta(q)\mapsto[q]_{R_\infty}$.
It does not by itself give an executable transition on $\eta(Q)$.
Such a summary quotient exists with the declared labels exactly when
$\ker(\eta)$ itself is an action congruence. In particular, legality,
definedness, status, terminal output, response, and contracted cost must
factor through $\eta$, and for every legal defined action there must be a
single successor function on its summary domain satisfying

$$
\overline T_a(\eta(q))=\eta(\operatorname{Next}(q,a)).
$$

Proof. Congruence makes every displayed definition independent of the
representative. Conversely, these factorizations imply all congruence
clauses. For failure of the weaker condition to suffice, take pending states
$x,y$ and halt states $z,w$ with the same row. The only progress action has
the same response and cost at $x,y$, and sends $x$ to $z$ and $y$ to $w$.
Put $\eta(x)=\eta(y)=0$, $\eta(z)=1$, and $\eta(w)=2$.
The pairs $x,y$ and $z,w$ have identical labelled futures, so the kernel
inclusion holds. But $\overline T_a(0)$ would have to be both $1$ and $2$.
Thus predictive safety does not imply successor-class factorization. ∎

**Definition 58.4 (completed fixed-policy residual).** Fix one deterministic
policy $\pi$ with source-independent visible-history updates. Fix one common
visible response alphabet $V$, including a symbol for every silent event, and
the common continuation carrier $V^{\ast}$. Responses index possible
successors; the controller does not choose the actual response.

A completed deterministic transducer has a state set $K_\pi^{\mathrm c}$,
a total response-indexed transition
$\delta_\pi:K_\pi^{\mathrm c}\times V\to K_\pi^{\mathrm c}$,
a state label $L_\pi$, and an edge label $B_\pi$. These contain:

1. a state status in
   $\{\mathsf{pending},\mathsf{halt},\mathsf{deadlock},
     \mathsf{illegal},\mathsf{undefined}\}$;
2. the selected primitive action, or the distinct instruction
   $\mathsf{halt}$ or $\mathsf{none}$;
3. the complete terminal output, absent outside a halt, and every contracted
   initial/final resource or accumulator label;
4. for each response $o$, an edge label $B_\pi(k,o)$ distinguishing admitted,
   illegal, and undefined continuations and recording every contracted
   event-resource label, together with the response-indexed successor
   $\delta_\pi(k,o)$. Successor state names are not output labels: their
   residuals are compared recursively.

A response outside the admitted response set goes to the labelled illegal
sink; an unspecified operation goes to a distinct undefined sink.
Additional responses after a halt or deadlock are tagged illegal. Sinks have
total absorbing transitions, no selected executable action, and no additional
resource contribution. These completion steps are mathematical padding, not
actual actions or additional legal traces. A selected action that is itself
illegal or undefined is marked as such before any response. On every admitted
branch, the actual next controller state must equal $\delta_\pi(k,o)$ for
every compatible source; separately chosen hidden-source successors do not
supply this factorization.

Every field being compared must have the stated deterministic factorization.
If a source-dependent field does not factor through the controller boundary,
it cannot silently be assigned a scalar value there. Either the contract
supplies the required factorization, or its semantic label retains the
whole source-indexed field, including its domain and absent cases, and equality
of that label is pointwise on the same sources. Such labels supply no new
online source-identity input. A proposed finite transducer with neither
representation does not satisfy this definition.

For $w=o_1\cdots o_n$, put $k_0=k$ and
$k_{i+1}=\delta_\pi(k_i,o_{i+1})$, and define the total trace function

$$
F^\pi_k(w)=
\bigl((L_\pi(k_i))_{i=0}^{n},
      (B_\pi(k_i,o_{i+1}))_{i=0}^{n-1}\bigr).
$$

Let $D^\pi_k\subseteq V^{\ast}$ be the prefix-closed domain of words all of
whose edges are admitted, including the empty word. The completed residual is

$$
\mathcal R^\pi_k=(D^\pi_k,F^\pi_k),\qquad
k\equiv_\pi k'
\quad\Longleftrightarrow\quad
D^\pi_k=D^\pi_{k'}\ \text{and}\
F^\pi_k(w)=F^\pi_{k'}(w)\ \text{for every }w\in V^{\ast}.
$$

Equality includes the admissible domains, all failure and termination tags,
selected actions, full terminal outputs, and the resource labels specified
by $\Gamma$. It never means comparison only on an intersection of
compatible-source continuation domains.

**Proposition 58.5 (residual congruence and its exact minimality scope).**
Completed-residual equality is an equivalence and a right congruence:

$$
k\equiv_\pi k'
\ \Longrightarrow\
L_\pi(k)=L_\pi(k'),\quad
B_\pi(k,o)=B_\pi(k',o),\quad
\delta_\pi(k,o)\equiv_\pi\delta_\pi(k',o)
\quad(o\in V).
$$

If the reachable completed transducer is finite, or its residual equivalence
has finite index, its residual quotient is a finite deterministic controller
preserving this completed action-labelled contract. It is minimal among
deterministic controllers preserving that same contract at every admitted
visible initial boundary on the entire completed continuation carrier. Completion sinks are counted by
the same convention in every compared controller. This is not a minimum
among all controllers merely solving the target or matching terminal outputs.

Proof. Equality of the pairs $\mathcal R^\pi_k$ is reflexive, symmetric,
and transitive. The empty word gives equality of state labels. The word $o$
gives the edge label, and deleting its first step from the traces at $ov$
gives equality of the successor residuals for every $v$; the domain derivatives
agree as well. The quotient is therefore well-defined. A finite distinguishing
word, or a domain/action/status/resource label at one of its prefixes,
separates every two distinct residual classes. Any implementation putting their
reaching visible histories in the same state would give identical derivatives
and could not preserve this contract. It needs at least one state per
reachable residual class; the quotient attains this bound. Since admitted
runs and complete outputs are preserved, success of the original policy is
also preserved. ∎

**Proposition 58.6 (intersection comparison is not transitive).** On the common
alphabet $\{x,y,z\}$, take the following partial output functions, all with
the same output at the empty word:

| Residual | Domain | Outputs at nonempty words |
| --- | --- | --- |
| $f_1$ | $\{\varepsilon,x,y\}$ | $f_1(x)=0,\ f_1(y)=0$ |
| $f_2$ | $\{\varepsilon,y,z\}$ | $f_2(y)=0,\ f_2(z)=0$ |
| $f_3$ | $\{\varepsilon,x,z\}$ | $f_3(x)=1,\ f_3(z)=0$ |

The rule “agree on the intersection of their domains” relates $f_1$ to $f_2$
and $f_2$ to $f_3$, but not $f_1$ to $f_3$.

Proof. The first two intersections test $y$ and $z$, respectively, where the
outputs agree. The third tests $x$, where they differ. Each intersection has a
nonempty word, so the failure is not due to a vacuous comparison. These are
prefix-closed one-response domains and can be realized by one-step partial
transducers. Tagging all missing continuations instead gives total residuals;
their equality compares domains and is transitive. ∎

**Assumption 58.7 (finite task-policy comparison).** For finite task
optimization, specify a nonempty finite family $\Pi_{\mathrm{fin}}$ of
admissible successful deterministic observation-based policies. For every
$\pi\in\Pi_{\mathrm{fin}}$, require a finite deterministic completed
$K_\pi^{\mathrm c}$ or, more generally, finite residual index

$$
n_\pi=\bigl|K_\pi^{\mathrm c}/\mathord{\equiv_\pi}\bigr|<\infty.
$$

Then $\min_{\pi\in\Pi_{\mathrm{fin}}}n_\pi$ is attained. An effective minimum
additionally requires effective presentation of the family and exact effective
residual equality or a certified finite quotient. A minimum over this family
is a global task minimum only if completeness for the intended controller
class has separately been proved. If success is not known in advance, start
with a finite candidate family and decide success under 58.11; its successful
subfamily must be nonempty before using this minimum.

Finite chart types and finite action/reply alphabets do not imply any of these
memory or index conditions. For example, after observing an initial unary
encoding of an arbitrary $n$, a policy may perform $n$ silent ticks and halt.
Its countdown states have distinct residuals, distinguished by the number of
ticks before halt, although its action and response alphabets are finite and
every actual countdown terminates. Finite graph size, finite residual index,
finite policy enumeration, and finite sourcewise resource bounds are separate
hypotheses.

**Proposition 58.8 (correct calibration obstruction).** In the calibration
example of Continuation II, all three singleton histories are pairwise
mergeable, with different common first actions for different pairs. The
three-way union is unsolvable. Thus this example disproves existence of a
coarsest successful history partition, not solvability of a two-way union.

Proof. The source is $(i,z)\in\{1,2,3\}\times\{0,1\}$ and the target is $z$.
The destructive experiment table is

| History | $a$ | $b$ | $c$ |
| --- | --- | --- | --- |
| $i=1$ | $z$ | $z$ | $\star$ |
| $i=2$ | $\star$ | $z$ | $z$ |
| $i=3$ | $z$ | $\star$ | $z$ |

Every experiment destroys the remaining target information after producing
its response; a $\star$ branch has no later recovery action. Each singleton
is solvable. Histories $\{1,2\}$ share first action $b$, $\{1,3\}$ share $a$,
and $\{2,3\}$ share $c$. On all three histories, every first action has a
$\star$ branch compatible with both target bits. Immediate halt is also
incorrect for one of the bits. Hence the three-way union has no successful
policy. The partitions $\{1,2\}\mid\{3\}$ and $\{1,3\}\mid\{2\}$ are feasible,
whereas every common coarsening merges all three and fails. Fixed-policy
minimization in 58.5 does not remove this incompatibility between policies. ∎

**Definition 58.9 (the aggregation law is part of the resource contract).**
A resource contract $\Gamma$ specifies the event fields being charged, their
units and domains, the initial accumulator, the ordered trace aggregation
$G_\Gamma$, its terminal evaluation, and any subsequent sourcewise
aggregation. Additive sum, maximum, position-dependent weighted sum, and
sourcewise supremum are different choices of $\Gamma$. For a policy and
one actual source $s$, first form its complete same-source trace
$\tau^\pi_s$ and its value $c^\pi_\Gamma(s)=G_\Gamma(\tau^\pi_s)$.
A worst-source objective can then be defined as
$\sup_{s\in S}c^\pi_\Gamma(s)$ on the declared source domain $S$.

When aggregation is recursive, all state needed for its update must be
retained, with the same initialization, update, and terminal rule in the
quotient. For a nonrecursive aggregation, preservation must cover its
whole input trace. Equal coarse event prices alone do not preserve an
aggregation that depends on an omitted event position, epoch, or source field.

**Proposition 58.10 (same-source resource preservation).** A congruence
preserves $\Gamma$ when, for each original source and each contracted trace,
the quotient preserves all inputs to $G_\Gamma$ and uses the same aggregation
law. It then preserves $c^\pi_\Gamma(s)$ for each $s$, and consequently the
declared sourcewise bounds on the same source domain.

Proof. For recursive aggregation, induct on actual events using the equal
initial accumulator, equal input labels, and equal update rule; apply the
same terminal evaluation. Otherwise apply the same function $G_\Gamma$ to
equal contracted traces. Pointwise equality permits the same outer supremum.
It does not permit assembling coordinates from different source traces.
For instance, two source costs $(1,0)$ and $(0,1)$ give
$\sup_s(c_1(s)+c_2(s))=1$, whereas
$\sup_s c_1(s)+\sup_s c_2(s)=2$. Thus a weighted same-run objective must be
formed before the source supremum, exactly as in Continuation IV §44.3. ∎

**Assumption 58.11 (conditional fixed-budget synthesis).** The
fixed-budget feasibility argument from
[FIB Relational Fiber Calculus · Continuation IV, §§41--44, corrected by §§46--50](FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_IV.md)
uses the finite-profile predicate of its §49 and requires the following
hypotheses, in addition to
the tagged, completed, observation-based, and $\Gamma$-preserving contracts
above.

1. There is a nonempty source-total domain covered by the specified finitely
   many chart types, with Presburger-definable parameter admission. Fix a
   finite controller-size bound $K$, finite action and response types, and a
   finite effectively enumerable family of controller tables, including the
   allowed instruction and terminal-output choices. A claim covering all
   controllers of size at most $K$ requires completeness of this enumeration.
2. Common-boundary legality, source-independent response-indexed control
   updates, and exact same-source semantics hold for the full ordered action
   language, including passive actions, interventions, and silent events.
   Complete target-row equality and correctness are preserved.
3. For each requested finite budget $B$, an independently certified
   effective raw-event horizon $T_K(B)$ is uniform over all admitted sources
   and response branches of every source-total budget-feasible candidate.
   A mixed finite-profile query additionally certifies one finite vector
   bounding every coordinate uniformly over sources, as in Continuation IV
   §§47.1--49. Alternatively, a certified regular-history encoding or exact
   acceleration decides source-total termination, complete terminal rows,
   and these finite uniform bounds. A merely per-source decreasing rank,
   response-phase bound, or plain regularity is insufficient.
4. Admission, replies, legality, definedness, successors, epoch updates,
   exact event costs, complete-row equality, and the pathwise resource
   thresholds for the chosen $\Gamma$ are effectively Presburger-definable,
   or the certified alternative supplies the same exact decisions.
5. All finite path predicates describe actual deterministic executions from
   the original source, and include every raw event through the halt.
   Source-total success means that every admitted source has such a legal,
   defined, correct terminal path. Separate existential witnesses on
   different source fibers do not supply this universal condition.

These assumptions decide the specified finite-budget feasibility by the
finite path argument in 58.21. Effective frontier extraction also requires
an exact finite-profile decision for every queried mixed box, including the
all-infinite box, as required by Continuation IV §§47--49. The historical
uncorrected §44.2 test used ordinary mixed feasibility in its place; 58.19
illustrates that distinction even with a finite uniform seed. For the
explicit finite-family implementation in 58.20, decide each candidate's
source-total success, decide uniform boundedness of every coordinate, and
extract exact finite bounds. Budget horizons $T_K(B)$ alone supply neither a
budget-independent family horizon nor those boundedness decisions. The
published repair requires them rather than deriving them from a per-source
rank. Weighted thresholds retain Continuation IV §50's finite-profile
restriction. Neither finite alphabets, a
semantic greatest quotient, nor existence of a finite residual quotient
alone proves effective synthesis, effective quotient computation, or an
unconditional decidability theorem.

**Definition 58.12 (measurable terminated record laws).** Fix one probability
space $(U,\mathcal U,\mu)$ and one common deterministic visible-response rule
after fixing the seed $u$. For each source $s$, let
$T_s:U\to\mathbb N\cup\{\infty\}$ be its measurable termination time and let
$X_s$ be its measurable complete record on $\{T_s<\infty\}$, taking values in
one declared measurable carrier $(X,\mathcal X)$. The carrier specifies every
field being compared, including selected actions, ordered addresses, status,
output, and resource values when these are part of the contract.

The measurability of $T_s$ and the complete $X_s$ is an assumption of this
record-law extension. Deterministic source-uniform execution does not supply
it on an arbitrary seed space. Likewise, per-source measurable null
wrong-return and divergence events and a measurable extended cost do not
by themselves assert measurable complete transcripts or factorization of
every source-dependent record field through the visible history.

A probability law on finite complete records requires $T_s<\infty$
almost surely for every admitted $s$. If nontermination is permitted, either
use the subprobability law

$$
K_s(B)=\mu\{u:T_s(u)<\infty,\ X_s(u)\in B\}
\quad(B\in\mathcal X),
$$

or extend the carrier by a measurable cemetery divergence record $\dagger$
and put $\widetilde X_s=\dagger$ on $\{T_s=\infty\}$. The latter convention
must declare which divergent fields are discarded or retained; it does not
assign a finite completed cost to an infinite trace. Almost-sure finite
termination gives neither a uniform finite horizon nor a finite expected
resource value.

**Proposition 58.13 (equal visible responses need not give equal full records).**
A common seed, a common visible rule, and equal visible prefixes determine
the same policy instructions and visible-memory updates wherever both are
defined. Equality of the full finite action history additionally requires
matching stopping/status behavior. These premises do not determine arbitrary
source-dependent record fields.

Proof. Let a one-action rule always receive response $0$ and halt with
output $0$. Let its event cost be $0$ at source $s$ and $1$ at source $t$.
All seeds and responses agree, while the complete resource records differ.
More generally, to conclude equality of complete records on a measurable
event $E$, require finite termination at both sources on $E$ and equality
almost everywhere there of every compared field. A sufficient hypothesis
is that each such field is the same measurable function of the seed and the
matched complete visible history, including the stopping/status information.
Induction determines the visible action/history record; the stated field
factorizations then determine the other fields. Without them, only the
record projection whose fields do factor can be compared this way. ∎

**Proposition 58.14 (event transport gives a common submeasure).** Let $E$ be
a measurable event on which both runs terminate finitely. Let $Y_s,Y_t$ be
measurable records on a common carrier that agree almost everywhere on $E$.
They may be the complete $X_s,X_t$ under the field conditions of 58.13, or
a declared observable projection of those records. Write $K_s^Y,K_t^Y$ for
their corresponding full or finite-termination laws. Then

$$
\nu_E(B)
=\mu(E\cap\{Y_s\in B\})
=\mu(E\cap\{Y_t\in B\})
\le K_s^Y(B),\ K_t^Y(B).
$$

Thus the event-transported pushforward is a common submeasure. With only
projected-record equality, this conclusion concerns the projected laws,
not the laws of the complete source-dependent records.

For finite measures $K_s^Y,K_t^Y$, their abstract meet is the greatest
measure dominated by both. In particular,

$$
\nu_E\le K_s^Y\wedge K_t^Y.
$$

This meet need not be the pushforward of any agreement event in the specified
common-seed coupling.

Proof. Restriction to $E$ proves both measure inequalities. To identify the
abstract meet, put $\lambda=K_s^Y+K_t^Y$, and let $f,g$ be the respective
Radon--Nikodym densities. Then

$$
(K_s^Y\wedge K_t^Y)(B)=\int_B\min(f,g)\,d\lambda.
$$

This measure is dominated by both laws. Any other common dominated measure
has a density bounded almost everywhere by both $f$ and $g$, hence by their
minimum. This proves maximality and the bound on $\nu_E$, but supplies no
agreement event for the chosen seed coupling. The same proof applies to
finite-termination subprobabilities; under the cemetery convention it applies
on the extended carrier. ∎

**Proposition 58.15 (four seeds do not attain the meet).** On
$U=\{1,2,3,4\}$ with uniform measure, define two finite record maps by

$$
\begin{aligned}
(Y_s(1),Y_s(2),Y_s(3),Y_s(4))&=(0,0,1,1),\\
(Y_t(1),Y_t(2),Y_t(3),Y_t(4))&=(0,1,0,1).
\end{aligned}
$$

Their laws and their abstract meet are all
$\tfrac12\delta_0+\tfrac12\delta_1$, of mass $1$. Every agreement event in
this coupling has mass at most $\tfrac12$.

Proof. Agreement occurs exactly at seeds $1$ and $4$, whose pushforward is
$\tfrac14\delta_0+\tfrac14\delta_1$. Every event giving pointwise agreement
is contained in these two seeds up to null sets. The remaining seeds produce
opposite records even though the marginal laws are identical. These maps
can be realized by a common one-read rule that returns its source-dependent
visible response and halts. Thus the common-seed requirement does not imply
that the coupling attains the abstract meet. ∎

**Proposition 58.16 (observation-based lifting and a sound workflow).**
Suppose a source-total exact action interface satisfies 58.2, has an actual
action-congruent summary as in 58.3, preserves the target/correctness contract
and $\Gamma$ on each original source, and admits a successful quotient policy.
Require this policy to be observation-based before lifting it: its action and
next controller memory must be selectable from the actual visible boundary
and received response, without a hidden source or chart coordinate. If a
quotient class is used as memory, its initialization and update must have
this same visible factorization.

Explicitly, with $h$ the available visible history, a sufficient condition
is an available map $\chi(h)$ to the actual quotient class such that

$$
\chi(h)=[q]\ \text{for every source state }q\text{ compatible with }h,
\qquad
\widehat\pi(h)=\overline\pi(\chi(h)),
$$

with a source-independent update from the current visible memory, selected
action, and observed response. If the whole class is not observable, lifting
is still possible when the chosen action and all required memory updates
factor through $h$ across every compatible class; these factorizations must
be supplied. A policy allowed to inspect an unobservable quotient class
does not lift merely because the semantic quotient exists.

Under these hypotheses, the sequence

$$
\text{action-congruent quotient}
\longrightarrow
\text{target acquisition}
\longrightarrow
\text{fixed-policy controller minimization}
\longrightarrow
\text{resource verification}
$$

is a sound workflow. Finite controller minimization requires 58.4--58.7;
effective fixed-budget resource decisions require 58.11, and 58.20 gives
one sufficient package for effective finite-family frontier extraction.
Randomized transport, when used, additionally requires 58.12--58.14.

Proof. Visible factorization gives one legal first action on every compatible
source. The observed response determines the same controller update, while
congruence determines the correct successor class. Induction gives an exact
same-source lift of every finite quotient run, preserving status, complete
output, and all contracted resource labels. The stipulated successful
termination and target contract therefore transfer to the original sources.
Apply 58.5 to the selected completed residual and 58.10 to its aggregation;
apply the finite synthesis argument only under 58.11.

This order is not logically forced. A successful observation-based controller
can be supplied first and then minimized and checked. Resource constraints can
also guide acquisition or be included in the quotient labels from the start.
These alternatives remain sound when they discharge the same factorization,
termination, residual, and resource obligations. ∎

**Convention 58.17 (mathematical scope and provenance).** The fixed-point and
deterministic residual-minimization principles are standard background, as
are the Radon--Nikodym description of the meet of finite measures.
The resource arguments use the following prior methods:

1. Christoph Haase, *A survival guide to Presburger arithmetic*,
   ACM SIGLOG News 5(3), 67--82,
   [doi:10.1145/3242953.3242964](https://doi.org/10.1145/3242953.3242964):
   Presburger decision procedures used on the exact path and boundedness
   formulas in 58.20--58.21.
2. Seymour Ginsburg and Edwin H. Spanier, *Semigroups, Presburger formulas,
   and languages*, Pacific Journal of Mathematics 16(2), 285--296,
   [doi:10.2140/pjm.1966.16.285](https://doi.org/10.2140/pjm.1966.16.285):
   the Presburger/semilinear background for effective integer-set descriptions.
3. Leonard E. Dickson, *Finiteness of the Odd Perfect and Primitive Abundant
   Numbers with n Distinct Prime Factors*, American Journal of Mathematics
   35(4), 413--422,
   [doi:10.2307/2370405](https://doi.org/10.2307/2370405):
   the classical finite-dimensional well-quasi-order principle used for
   existence in 58.21.

Their use here makes the action, source, residual, and aggregation
hypotheses explicit. The finite-profile and mixed-box repair, uniform
source-total history requirements, all-infinite decision, and weighted
restriction are already supplied by Relational IV §§46--50. Section 58.18
uses a distinct name for its corrected finite-profile predicate; 58.19 is a
concrete illustration of the historical failure, and 58.20 is an explicit
sufficient implementation of the published corrected interface for a
certified finite candidate family. These resource clauses reuse the
published repair and classical decision methods; they are not new general
feasibility discoveries in this volume. No priority claim is made.
All statements in §58 are ordinary mathematical definitions and arguments.
Neither the stochastic comparison in §55.3 nor a reference to results in
another volume certifies an exact Lean application of this contract.
The existing deterministic
[KBonacci acquisition contract](../../../D5/S3/ObserverMemory/Algorithms/KBonacciIrreversibleAcquisition.lean)
does not supply a measurable random full-record extension. The
[ActualTree per-source RandomContract](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean)
assumes measurable wrong-return and divergence events of measure zero and
measurable extended cost for each source; it does not assume measurable
complete records or the field factorizations required in 58.12--58.13.
No Lean/kernel-verification claim is made. Construction and effective
presentation of an appropriate action-closed interface for a general signed
FIB fibre remain separate unresolved obligations, as in §57.

**Definition 58.18 (finite-vector versus ordinary mixed feasibility).**
Use Relational IV §§46--49's corrected finite-profile contract, with the
following notation separating it from the historical ordinary mixed test.
Fix $d\ge1$, a nonempty source domain $D$, and an admissible controller class
$\mathcal C$. Let $\mathcal C_{\mathrm{ok}}$ consist of controllers that are
legal, defined, terminating and correct on every source. For such $C$, the
same-source resource contract gives $c_C(s)\in\mathbb N^d$. Define

$$
b_i(C)=\sup_{s\in D}c_{C,i}(s)\in\mathbb N\cup\{\infty\},
\qquad
\mathcal F=\{x\in\mathbb N^d:\exists C\in\mathcal C_{\mathrm{ok}},\
                         b(C)\le x\}.
$$

For $B\in(\mathbb N\cup\{\infty\})^d$, distinguish

$$
\begin{aligned}
\operatorname{MixFeas}(B)
  &\Longleftrightarrow
       \exists C\in\mathcal C_{\mathrm{ok}},\ b(C)\le B,\\
\operatorname{FinBox}(B)
  &\Longleftrightarrow
       \exists x\in\mathcal F,\ x\le B\\
  &\Longleftrightarrow
       \exists C\in\mathcal C_{\mathrm{ok}},\
          b(C)\in\mathbb N^d,\ b(C)\le B.
\end{aligned}
$$

The last equivalence follows by using $b(C)$ itself as $x$, or by taking
the controller witnessing $x$. Thus $\operatorname{FinBox}(B)$ implies
$\operatorname{MixFeas}(B)$, and they coincide when every coordinate of
$B$ is finite. An infinite coordinate of $B$ imposes no uniform finite
bound on that coordinate in $\operatorname{MixFeas}$.

For a nonempty finite $A\subseteq\mathcal F$ with $0\notin A$, choose for
each $v\in A$ a coordinate $f(v)$ with $v_{f(v)}>0$, and put

$$
B_i^f=\min\{v_i-1:v\in A,\ f(v)=i\},
\qquad \min\varnothing=\infty.
$$

For a finite vector $x$, being outside $\uparrow A$ means that for every
$v\in A$ at least one coordinate of $x$ is smaller than that of $v$.
Choosing such a coordinate places $x$ in one of these mixed boxes.
Conversely, membership in any such box gives a strict coordinate inequality
against every $v\in A$.
Consequently the valid identity is

$$
\exists x\in\mathcal F\setminus\uparrow A
\quad\Longleftrightarrow\quad
\bigvee_f\operatorname{FinBox}(B^f).
$$

If $0\in A$, the left side is false. If $A$ is empty, it is equivalent to
$\mathcal F\ne\varnothing$. A decision/extraction oracle for
$\operatorname{FinBox}$ must explicitly return a finite vector with a
uniformly bounded controller witness, or decide that none exists.
An oracle for $\operatorname{MixFeas}$ has a different contract.
Here $\operatorname{FinBox}$ is exactly the finite-profile feasibility
predicate of Relational IV §49, not an additional feasibility notion required
by the repair. Its all-infinite query has the exact decision meaning of IV §48.

**Proposition 58.19 (a mixed witness outside the finite frontier test).**
Let the source be $(n,z)\in\mathbb N\times\{0,1\}$, with target $z$.
The admissible candidate family consists exactly of

$$
C_a=a;\mathsf{halt}(z),
\qquad C_b=b;\mathsf{halt}(z).
$$

Both actions are legal, reveal $z$, and are followed by a zero-cost halt
with that output. Their action costs are

$$
c_{C_a}(n,z)=(1,n),
\qquad c_{C_b}(n,z)=(2,2).
$$

This has finite candidate, action and reply sets, source-total deterministic
Presburger semantics, and a uniform raw-event horizon $2$, including the halt.
The candidate $C_b$
supplies a finite uniform feasible seed. Nevertheless, for $A=\{(2,2)\}$,

$$
\mathcal F=\uparrow\{(2,2)\},
\qquad
\operatorname{MixFeas}((1,\infty))\ \text{holds},
\qquad
\mathcal F\setminus\uparrow A=\varnothing.
$$

Proof. Source admission is $n\ge0$ and $z=0$ or $z=1$.
The reply is $z$; a single reply-indexed rule selects the matching halt
output, independent of $n$. All admission, reply, transition, complete-row
equality and cost relations are Presburger, and every run has exactly two
events. Both candidates are source-total and correct. Their coordinatewise
uniform bounds are

$$
b(C_a)=(1,\infty),
\qquad b(C_b)=(2,2).
$$

For every finite second-coordinate bound $M$, the source $(M+1,0)$ violates
it under $C_a$. Thus no finite budget is feasible through $C_a$.
$C_b$ is feasible exactly at finite budgets dominating $(2,2)$, proving
the displayed finite region and the empty difference. In contrast $C_a$
satisfies the mixed box $(1,\infty)$ on every source. Choosing the first
coordinate of $(2,2)$ in the box construction of 58.18 produces that very
box. Hence the historical uncorrected §44.2 ordinary mixed test has a true
right side and a false finite-vector left side. The effective IV §§47--49
predicate rejects this witness because $C_a$ lacks a finite second-coordinate
bound. This example instantiates the failure already delimited there: horizon
bounds control event count, not cost magnitudes over the source domain. ∎

**Theorem 58.20 (explicit sufficient implementation of the corrected finite-profile interface).**
For a certified finite candidate family, the following implements the
published Relational IV §§47--49 interface by exact success and boundedness
decisions. It is a sufficient construction relative to that family.
Use 58.18's nonempty source domain and integer resource contract. Suppose:

1. The admissible family $\mathcal C$ is finite and effectively listed,
   with exact deterministic observation-based same-source semantics.
2. For every candidate, whether it is legal, defined, terminating and
   complete target-row correct on every source is decidable.
3. For every successful candidate and every coordinate, existence of a finite
   uniform bound is decidable; whenever bounded, its exact least uniform
   bound $b_i(C)$ can be computed.

Then the finite-budget feasible region, including emptiness, has an effectively
computable minimal basis. Decide success of every candidate, discard the
unsuccessful candidates and every successful candidate with any unbounded
coordinate, and compute the vectors of the remaining candidates. If
$\mathcal V$ is the resulting finite set, return

$$
\mathcal B=\{v\in\mathcal V:
       \nexists w\in\mathcal V,\ w\le v,\ w\ne v\}.
$$

Then $\mathcal F=\uparrow\mathcal B$. For every mixed box,
$\operatorname{FinBox}(B)$ is decided by testing $v\le B$ for
$v\in\mathcal B$, with a retained controller as witness when true.
This conclusion is relative to the listed candidate family. It applies
to a larger controller class only with a separately proved complete
enumeration for that class.

Proof. The three hypotheses make every step terminate. An unsuccessful
candidate witnesses no element of $\mathcal F$. A successful candidate
with an unbounded coordinate fits no finite vector either. For every
remaining candidate, exact coordinatewise bounds give

$$
b(C)\le x
\quad\Longleftrightarrow\quad
\forall s\in D,\ \forall i,\ c_{C,i}(s)\le x_i.
$$

Thus $\mathcal F=\uparrow\mathcal V$. Every vector in the finite set
$\mathcal V$ dominates one of its minimal vectors, so removing strict
dominators and duplicate vectors gives $\uparrow\mathcal B=\uparrow\mathcal V$.
The same observation and 58.18 give the asserted exact finite-box test.
Different coordinates of $b(C)$ may be attained at different sources;
the argument concerns coordinatewise budget bounds, not a same-source
weighted objective.

Here is one sufficient effective Presburger package for hypotheses 2--3.
In addition to 58.11's finite family and exact semantics, require an
independently certified computable $H_*$ such that every run of every
source-total successful candidate in that family has at most $H_*$
raw events, including halt, irrespective of its resource vector.
This is one budget-independent horizon for the whole successful family.
Require effectively constructed Presburger path predicates, with finite
tuples of auxiliary variables, for every candidate path of length at most
$H_*$. They must describe exactly its legal, defined same-source execution
from the initial boundary, its halt row, and its full aggregated integer
cost vector. Any aggregation used here must have this Presburger graph;
Presburger event prices alone do not certify an arbitrary aggregation.

For candidate $C$, let $P_{C,p}(s,\xi)$ be such a terminal-path predicate,
where $\xi$ includes the terminal row and the cost vector. Its correct
terminal-path coverage condition is the Presburger sentence

$$
\forall s\,
\left(D(s)\Longrightarrow
  \bigvee_{p:\,|p|\le H_*}
     \exists\xi\,\bigl(P_{C,p}(s,\xi)
                     \land \operatorname{Row}(\xi)=g(s)\bigr)\right).
$$

Every path includes its halt, and paths after a halt are not admitted.
On a finite union of chart types the formula is formed separately for
each chart and conjoined. Determinism and exactness ensure that its
witnesses are the actual source runs. The sentence therefore implies
source-total success. Conversely, success and the $H_*$ certificate
supply a witness for every source. It decides hypothesis 2, rejecting
nontermination and other failures through lack of correct terminal coverage.

For a successful $C$, project the finite disjunction of its correct
terminal-path predicates to the cost vector:

$$
\Phi_C(t)\Longleftrightarrow
 \bigvee_{p:\,|p|\le H_*}\exists s,\xi\,
 \bigl(D(s)\land P_{C,p}(s,\xi)
       \land\operatorname{Row}(\xi)=g(s)
       \land \operatorname{Cost}(\xi)=t\bigr).
$$

This is a Presburger formula defining exactly the nonempty set
$\{c_C(s):s\in D\}$. For coordinate $i$, decide the sentence

$$
\exists M\in\mathbb N\ \forall t\in\mathbb N^d,\
       \bigl(\Phi_C(t)\Longrightarrow t_i\le M\bigr).
$$

If it is false, that coordinate is unbounded and the candidate is discarded.
If it is true, test $m=0,1,2,\ldots$ until
$\neg\exists t\,(\Phi_C(t)\land t_i>m)$ holds. This search terminates
because boundedness has already been decided. The first such $m$ is
the exact least uniform bound $b_i(C)$. A nonempty bounded subset of
$\mathbb N$ has a maximum, so this value is attained in that coordinate;
a Presburger witness can also identify a source/path attaining it.
This proves hypothesis 3 using the prior Presburger decision method cited
in 58.17, without invoking ordinary mixed feasibility.

An exact termination and resource-range decision procedure from a certified
regular encoding or acceleration may instead supply hypotheses 2--3.
Its uniform boundedness decision and bound extraction must be part of
the certificate, not inferred from regularity. In particular, knowing
$T_K(B)$ for each constrained budget does not, without an additional
argument, supply $H_*$ or a decision of
$\exists M\,\forall s\,c_{C,i}(s)\le M$. Proposition 58.19 meets the
stronger horizon package: this algorithm discards $C_a$ and returns
$\mathcal B=\{(2,2)\}$. ∎

**Proposition 58.21 (fixed-budget decision and basis existence under the published repair).**
Under 58.11, feasibility of each specified finite budget is decidable.
A mixed finite-profile budget is decidable when its certificate also decides
the existence of a finite uniform bound in every coordinate, as in IV
§§47--49. An ordinary mixed query, if separately requested, uses
$\operatorname{MixFeas}$ and requires its own exact horizon or decision
certificate; it is not the effective IV frontier predicate. Independently, for any
controller class with the source-total integer semantics of 58.18 and
fixed finite $d$, the finite-budget region has a finite minimal basis,
possibly empty. The latter is an existence result, not an effective
frontier algorithm under 58.11 alone.

Proof. For a fixed budget $B$, enumerate the finite candidate family and
its exact terminal paths up to $T_K(B)$. For each candidate, form the
universal source-coverage sentence used in 58.20, now conjoining the
path's cost bounds in every constrained coordinate. Presburger
decidability decides this sentence; a finite disjunction over candidates
decides feasibility and selects a candidate when true. Exact paths and
universal source coverage prove soundness. The independent horizon
covering every successful budget-feasible candidate proves completeness.
The certified alternative must supply the same exact decision, including
termination. For a mixed finite-profile query, constrained pathwise bounds
alone do not enforce boundedness in unconstrained coordinates; the
$\operatorname{FinBox}$ certificate must provide that additional exact
decision. No all-infinite decision follows from horizons specified only for
budgets with a constrained coordinate. Relational IV §48 explicitly requires
this decision as an additional hypothesis, and 58.20 supplies it for its
certified finite family.

For basis existence, $\mathcal F\subseteq\mathbb N^d$ is upward closed by
its definition: a controller fitting $x$ also fits every larger vector.
Its minimal elements form an antichain, which is finite by the classical
Dickson principle cited in 58.17. Every $x\in\mathcal F$ has a minimal
element below it: the nonempty set
$\{y\in\mathcal F:y\le x\}$ lies in a finite lower box, and any minimal
element there is also globally minimal. Hence

$$
\mathcal F=\uparrow\operatorname{Min}(\mathcal F).
$$

If $\mathcal F=\varnothing$, the basis is empty. This proof does not
decide emptiness, locate the minimal elements, or provide an exact
outside-closure test. It requires neither a finite seed nor a finite
candidate family for existence. The effective conclusion for a finite
family uses the additional decisions in 58.20; 58.19 rules out replacing
them by the historical uncorrected mixed test in IV §44.2. The active
finite-profile predicate and weighted restriction remain those of IV
§§47--50. These are paper proofs under the
declared mathematical premises, with no Lean/kernel verification or
unconditional general signed-fiber construction. ∎

## 追加锚（本行以下为增补区）

## 59. Future root prediction from noisy old passive curves

**Definition 59.1 (the original source and the two comparison preparations).**
In this section Holographic IV denotes the
[immutable supplier text, §§109--110](https://github.com/the-omega-institute/trureturing/blob/0cd2d8e87296269efebb3d308ff59318aab0a10a/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md#109-a-persistent-centered-defect-for-actual-ancestry-transport).
Use the original ordered substitution sources $T_n=\rho^n(\alpha)$ and all
occurrence vertices of each source, with

$$
N_n=|V_{T_n}|=2F_{n+1}-1,\qquad
F_0=0,\quad F_1=1,\quad F_{j+2}=F_{j+1}+F_j.
$$

On the real counting space $\mathcal V_n=\ell^2(V_{T_n})$, let $L_n$ be the
closed unit-edge Laplacian, without a root killing term, and let $P_n$ be
orthogonal projection onto the zero-counting-mean subspace. Retain precisely
the actual ancestry pullback $J_n$ of Holographic IV, Definitions 109.1
and 110.1, which fixes old vertices and copies each old beta parent's value
to both its new children. Write

$$
S_n(a)=e^{-N_naL_n},\qquad
\mathcal C_nf=\sqrt{N_n}\,f(r),\qquad
\mathcal A_n=\sqrt{\frac{N_n}{N_{n+1}}}\,P_{n+1}J_nP_n.
$$

The operators and norms use every occurrence and counting measure. In
particular $\mathcal C_n$ and $\mathcal A_n$ are the normalized port and
ancestry comparison map, not the scalar finite-part quantities of
Holographic IV §92. Every root or root-neighbor smoothing norm below
restricts its input to $P_n\mathcal V_n$; the full closed counting
Laplacian and all occurrence vertices are retained.
Let $x_n\in P_n\mathcal V_n$, $n\ge2$, be the centered
unit vectors supplied by its Definition 110.1. The two preparations in this
section are $0$ and $x_n$ on the **same** deterministic old source $T_n$;
there is no probability law or mixture over sources or preparations.

Fix $a_0>0$. The optimistic old observation is the entire passive root curve

$$
\eta_n(f)(a)=\mathcal C_nS_n(a)f\quad(a\ge a_0),\qquad
\eta_n(f)\in\mathscr Y:=C_b([a_0,\infty),\mathbb R),
\quad \|y\|_\infty=\sup_{a\ge a_0}|y(a)|.
$$

Continuity follows from the finite-dimensional heat semigroup; boundedness
follows from contraction and the positive-time root smoothing bound of
Holographic IV (110.11). A supplied finite bank at declared times
$a_1,\ldots,a_m\ge a_0$ is the projection
$y\mapsto(y(a_1),\ldots,y(a_m))$, with maximum norm. Giving the entire curve
is a stronger comparison observation than giving this bank; it asserts no
native acquisition of either one.

Choose one fixed $s$ in the positive window $[s_*/2,s_*]$ of Holographic IV
Theorem 110.3, independently of $n$, and put

$$
g_{n,s}(f)=\mathcal C_{n+1}S_{n+1}(s)\mathcal A_nf,\qquad
q_n=|g_{n,s}(x_n)-g_{n,s}(0)|=|g_{n,s}(x_n)|.
$$

The actual chronological order of this target is ancestry comparison,
successor heat, then successor root readout. The supplier proves

$$
g_{n,s}(x_n)\longrightarrow D(s)\ne0,\qquad
q_n\longrightarrow |D(s)|>0,\qquad g_{n,s}(0)=0.
$$

The choice of the fixed window is essential: nonvanishing is not asserted
at every positive $s$, at a particular numerical time, or through $s=0$.

**Definition 59.2 (one common adversarial report contract).** Define the old
curve separation, a distance rather than a time, by

$$
a_n=\|\eta_n(x_n)-\eta_n(0)\|_\infty.
$$

At a prescribed radius $E\ge0$, every $y\in\mathscr Y$ with
$\|y-\eta_n(f)\|_\infty\le E$ is an allowed report for preparation $f$.
Both preparations use this same report channel. The report is the only
state-dependent datum: stopping, timing, and class tags cannot distinguish
preparations with the same report. For arbitrary predictor maps
$\widehat g_n:\mathscr Y\to\mathbb R$, define

$$
R_n(E)=\inf_{\widehat g_n}\;
 \max_{f\in\{0,x_n\}}\;
 \sup_{\substack{y\in\mathscr Y\\
                 \|y-\eta_n(f)\|_\infty\le E}}
 |\widehat g_n(y)-g_{n,s}(f)|.
$$

A predictor may depend on $n$, $a_0$, and $s$, and need not be linear,
continuous, measurable, or effectively computable. This grants the source
comparison metadata to strengthen the impossibility statement; it does not
make $n$ or $N_n$ a freely acquired native observation. The channel contract
is adversarial absolute error, not a stochastic noise model.

**Theorem 59.3 (the FIB future-readout noise and precision transfer).**
For the preparations, fixed times, normalization, and common report channel
of Definitions 59.1--59.2, there are $K_{\rm sharp}>0$ and $n_0\ge3$,
independent of $n$, such that

$$
a_n\le\frac{K_{\rm sharp}n}{N_n}\quad(n\ge n_0).
\tag{59.1}
$$

For every $n\ge2$ and $E\ge0$, the exact risk on these two preparations is

$$
R_n(E)=
\begin{cases}
0,&2E<a_n,\\
q_n/2,&2E\ge a_n.
\end{cases}
\tag{59.2}
$$

Consequently, the vanishing choice $E_n=a_n/2$ satisfies

$$
E_n\longrightarrow0,\qquad
R_n(E_n)\longrightarrow\frac{|D(s)|}{2}>0.
\tag{59.3}
$$

Every radius sequence with $E_n\ge K_{\rm sharp}n/(2N_n)$ for all
sufficiently large $n$ has the same limiting risk.

If $0\le\delta<|D(s)|/2$, any family of predictors guaranteeing worst error
at most $\delta$ on both preparations and every allowed report for all
sufficiently large $n$ must satisfy, eventually,

$$
2E_n<a_n\le\frac{K_{\rm sharp}n}{N_n}.
\tag{59.4}
$$

In particular, for the dyadic absolute-error radius $E_n=2^{-p_n}$,

$$
p_n>\log_2N_n-\log_2n+1-\log_2K_{\rm sharp},\qquad
\liminf_{n\to\infty}\frac{p_n}{n}\ge\log_2\varphi,
\quad \varphi=\frac{1+\sqrt5}{2}.
\tag{59.5}
$$

The overlap bounds also hold for any supplied finite bank in Definition
59.1 under its common maximum-norm error contract, since the bank separation
is no greater than $a_n$. Thus (59.5) remains a necessary condition for such
a bank to give the same guarantee; the bank can require still finer error
or have zero separation and prevent the guarantee even at zero radius.

Proof. Retain the exact old-field identity of Holographic IV (109.9),
with the witness normalization (109.7)--(109.8) and (110.2). For all
sufficiently large $n\ge3$, it says

$$
\begin{aligned}
x_n&=\frac{L_nH_n+P_nR_n^{\rm old}}{d_n},\\
R_n^{\rm old}
 &=u_{n,L}\delta_{v_{n,L}}+u_{n,R}\delta_{v_{n,R}},\\
\|H_n\|&\le h n\sqrt{N_n},\qquad
d_n\ge d_*\sqrt{N_n},\qquad
|u_{n,L}|+|u_{n,R}|\le U,
\end{aligned}
$$

for constants $h,d_*,U>0$ independent of $n$. Here $v_{n,L}$ and
$v_{n,R}$ are the two actual old root neighbors, and their deltas are
**node** point masses, not edge coordinates or successor vertices.
In the supplier's notation the coefficients are
$u_{n,L}=\alpha_nQ_{n-1}$ and $u_{n,R}=\beta_nQ_{n-2}$, where $Q_k$
denotes its block beta-charge sum $q_k$ from (108.10), with $|Q_k|\le2$;
this $Q_k$ is distinct from the future target gap $q_n$ here.
The contrast constants $\alpha_n,\beta_n$ are bounded by (109.5), and
$d_n/\sqrt{N_n}\to\sqrt{\kappa}>0$ by (109.8), where
$\kappa=c(2-c)$ and $c=\varphi^{-1}$. The corrector is zero
at the global root and both old subtree roots, so the two exterior root
seams contribute zero. Thus the two-neighbor support is an exact identity
on the old source, available eventually with $n_0\ge3$.
Choose $n_0$ so that all displayed bounds hold for every $n\ge n_0$.
Applying $P_n$ to (109.9) retains $P_nR_n^{\rm old}$ and uses
$P_nL_n=L_n$; the raw residual need not be centered.

Set $t=a_0/2$. The root port bound (110.11) gives

$$
\|\mathcal C_nS_n(t)\|\le B_t=\frac{V}{\sqrt{2et}},\qquad
V=\sup_j\|v_j^{\mathrm e}\|<\infty\quad(t>0),
$$

where $v_j^{\mathrm e}$ is the supplier's common-edge-carrier vector.
For either actual root neighbor $v$, write
$\mathcal C_{n,v}u=\sqrt{N_n}\,u(v)$ on $P_n\mathcal V_n$.
The unit-edge energy identity $L_n=D_n^*D_n$ of (103.1) gives, for
every centered $u$,

$$
|u(v)-u(r)|^2
 \le\sum_{\{w,w'\}\in E(T_n)}|u(w)-u(w')|^2
 =\|L_n^{1/2}u\|^2.
$$

Finite spectral calculus, on this same counting space, gives

$$
\sqrt{N_n}\,\|L_n^{1/2}S_n(t)\|
 \le\sqrt{N_n}\sup_{\lambda\ge0}
           \sqrt\lambda\,e^{-N_nt\lambda}
 =\frac1{\sqrt{2et}}.
$$

Consequently both neighbor ports satisfy

$$
\|\mathcal C_{n,v}S_n(t)\|
 \le B_t+\frac1{\sqrt{2et}}
 =\frac{V+1}{\sqrt{2et}}=:J_t.
$$

The representing vector of $\mathcal C_{n,v}$ on the centered subspace
is $\sqrt{N_n}P_n\delta_v$. Self-adjointness of $S_n(t)$ on that
subspace therefore yields

$$
\|S_n(t)P_n\delta_v\|
 =\frac{\|\mathcal C_{n,v}S_n(t)\|}{\sqrt{N_n}}
 \le\frac{J_t}{\sqrt{N_n}},\qquad
\|S_n(t)P_nR_n^{\rm old}\|
 \le\frac{UJ_t}{\sqrt{N_n}}.
$$

Keeping the support before smoothing supplies this extra
$N_n^{-1/2}$ factor. Bounding only $\|R_n^{\rm old}\|$ as in (109.10)
loses it. With $\|L_nS_n(t)\|\le1/(eN_nt)$, the exact field identity
now gives

$$
\|S_n(t)x_n\|
 \le\frac{\|L_nS_n(t)H_n\|
             +\|S_n(t)P_nR_n^{\rm old}\|}{d_n}
 \le\frac1{d_*N_n}
           \left(\frac{hn}{et}+UJ_t\right)
 \quad(n\ge n_0).
\tag{59.6}
$$

The positive semidefinite closed Laplacian makes $S_n$ a contraction
on the centered counting space. For every $a\ge a_0=2t$, split the heat:

$$
\begin{aligned}
|\mathcal C_nS_n(a)x_n|
 &\le\|\mathcal C_nS_n(t)\|\,\|S_n(a-t)x_n\|\\
 &\le B_t\,\|S_n(t)x_n\|\\
 &\le\frac{B_t}{d_*N_n}
          \left(\frac{hn}{et}+UJ_t\right)
 \le\frac{K_{\rm sharp}n}{N_n}.
\end{aligned}
\tag{59.7}
$$

The second inequality uses
$S_n(a-t)=S_n(a-2t)S_n(t)$ and $a-2t\ge0$.
It therefore covers the entire unbounded interval $[a_0,\infty)$, without
assuming that the supplier's compact-interval convergence is already
uniform there. Choose any positive

$$
K_{\rm sharp}\ge\frac{B_t}{d_*}
              \left(\frac h{et}+\frac{UJ_t}{n_0}\right).
$$

Taking the supremum in (59.7) proves (59.1), since $\eta_n(0)=0$.
The constants depend on $a_0$ and the fixed supplier family, not on $n$.
These root and neighbor smoothing bounds do not hold on the full space:
$S_n(t)$ fixes the constant mode, and the normalized ports take value $1$
on $N_n^{-1/2}\mathbf1$. Their full-space norms are therefore at least
$1$ for every $t$, whereas $B_t,J_t\to0$ as $t\to\infty$.
The projection $P_n$ and centered operator domains are essential.

For the noise step, the bounded continuous midpoint curve

$$
y_n^*=\frac{\eta_n(x_n)+\eta_n(0)}2
$$

has distance exactly $a_n/2$ from both true curves. When $2E\ge a_n$ it
is an allowed report for both preparations. Any predictor therefore assigns
the same number $z=\widehat g_n(y_n^*)$ to two targets separated by $q_n$.
The triangle inequality gives

$$
q_n\le |z-g_{n,s}(0)|+|z-g_{n,s}(x_n)|
 \le 2\max_{f\in\{0,x_n\}}|z-g_{n,s}(f)|.
$$

Taking the allowed-report supremum and then the infimum over predictor maps
proves $R_n(E)\ge q_n/2$ whenever $2E\ge a_n$.
The constant target-midpoint predictor
$\widehat g_n(y)=[g_{n,s}(0)+g_{n,s}(x_n)]/2$ has error exactly
$q_n/2$ on both preparations for every report, proving equality in this
branch. When $2E<a_n$, the two full closed report balls are disjoint:
a point in their intersection would give $a_n\le2E$ by the triangle
inequality. On their union, assign to each report the target of its unique
compatible preparation, and assign any value outside the union. This
arbitrary predictor has zero error. These two branches prove (59.2)
as an elementary classical intermediate for this source comparison;
the decoder is not claimed measurable or effective.
The shared-report midpoint/radius-of-information step is a classical
optimal-recovery ingredient; see Micchelli and Rivlin, *A Survey of Optimal
Recovery*, in *Optimal Estimation in Approximation Theory*,
[doi:10.1007/978-1-4684-2388-4_1](https://doi.org/10.1007/978-1-4684-2388-4_1),
and the bounded-error optimal-recovery setting of Foucart and Liao,
*Optimal Recovery from Inaccurate Data in Hilbert Spaces: Regularize, But
What of the Parameter?*,
[doi:10.1007/s00365-022-09590-5](https://doi.org/10.1007/s00365-022-09590-5).
The same two-consistent-input triangle-inequality step appears explicitly in
the proof of Theorem 1 of Foucart, *Learning the maximum of a Hölder function
from inexact data*,
[doi:10.1090/proc/17456](https://doi.org/10.1090/proc/17456).
Only that lower-bound ingredient is used: no sufficient recovery theorem,
Hilbert-space regularization rule, or Hölder-model hypothesis is transferred
to the curve carrier. The displayed argument proves the needed step directly.

Binet's formula and $N_n=2F_{n+1}-1$ give

$$
\frac n{N_n}\longrightarrow0,\qquad
\frac{\log_2N_n}{n}\longrightarrow\log_2\varphi,\qquad
\frac{\log_2n}{n}\longrightarrow0.
$$

Thus (59.1) implies $a_n\to0$, whereas the supplier's fixed-$s$ limit
gives $q_n\to|D(s)|>0$. By (59.2), substituting $E_n=a_n/2$ gives
$R_n(E_n)=q_n/2$, proving (59.3).
If $E_n\ge K_{\rm sharp}n/(2N_n)$, (59.1) also implies $2E_n\ge a_n$,
so the same exact risk and limit hold eventually.
For a fixed $\delta<|D(s)|/2$, eventually $q_n>2\delta$.
Then overlapping report balls would contradict a worst-error guarantee of
$\delta$ by (59.2), proving (59.4). With $E_n=2^{-p_n}$, (59.4) gives
$2^{1-p_n}<K_{\rm sharp}n/N_n$. Taking logarithms of these positive
quantities and using the displayed growth limits proves (59.5).
For a finite bank its projected midpoint is again allowed at both
preparations, and its separation is bounded by the full-curve separation;
the same argument applies. $\square$

**Convention 59.4 (scope, degeneracies, and provenance).** If $a_n=0$ at
some finite $n$ with $q_n>0$, even the zero-radius report is shared and
$R_n(0)=q_n/2$. If $a_n>0$, however, $E_n=a_n/4$ gives zero two-state
risk by (59.2); along indices with positive separation these radii also
tend to zero. In particular, if $a_n>0$ eventually, this is a vanishing
noise sequence with eventually zero risk, so vanishing noise alone does
not force failure under that condition.
The theorem takes no logarithm of $a_n$ and presumes no strictly positive
finite-$n$ old curve gap. Its arbitrary two-point decoder supplies neither
recovery on the entire original source or field domain nor a finite
actual-history acquisition procedure.

The exponent in (59.5) is necessary for the declared dyadic **absolute-error
radius** under this common channel. No matching lower bound on $a_n$ or
general-domain recovery upper bound is supplied, so this exponent is not
claimed optimal. It is not a sufficient precision algorithm or a storage
optimum: it counts neither representations of an entire curve nor acquired
index metadata. It supplies no physical energy or
duration law. The observation cutoff $a_0$ and successor readout time $s$
are fixed positive comparison times; the proof supplies no uniform bound
as $a_0\downarrow0$, and no conclusion is drawn for observation times tending
to zero with $n$.

Normalization is part of the target. With ordinary unnormalized successor
root evaluation on the same unit counting-norm inputs and map $\mathcal A_n$,
$g_{n,s}(x_n)$ is divided by $\sqrt{N_{n+1}}$ and tends to zero, as in
Holographic IV §110.5. That target does not have the fixed positive gap used
in (59.3)--(59.5). Changing instead to the pointwise fields
$\sqrt{N_n}x_n$ changes the input scale and its noise contract; it is not
an unchanged precision claim.

This is `repo-derived` source-specific composition of Holographic IV
(109.7)--(109.10) and §§110.1--110.5, using its unit-edge identity (103.1),
with the cited `literature-attested` optimal-recovery ingredient;
no claim of originality is made for the composition. The
uncertainty here is between signed homogeneous preparations, not between
two native root-query replies or two separate source-size experiments.
Native preparation of these signed fields and realization of heat, both
centering projections, ancestry transfer, and real root ports through $\mathsf{Read}$ and
$\mathsf{ApplyRho}$ remain unproved. A bridge would have to preserve the
same actual source and joint action history, immutable target, epoch and
presence guards, permissions and refusals, absorbing Stop, and every
declared preparation, acquisition, address, update, arithmetic, memory, and
output cost required by Holographic IV §110.5. Comparison time remains
separate from physical duration until that correspondence is proved.
These are ordinary paper statements, without a Lean/kernel-verification
claim.

## 追加锚（本行以下为增补区）
