# Acquired source compatibility and source-preserving retry

## 1. Numerical queries, acquired records and the upper-proposal task

**Definition 1.1 (a passive source with a finite address interface).**
Fix public integers $N,t$ with $0\le t<N$, put $A=\{1,\ldots,N\}$,
and let $\binom At$ be the set of $t$-element subsets of $A$.
The source space, numerical target and response function are

$$
\begin{aligned}
X_{N,t}&=\{b\}\sqcup\bigl(\mathbb N_{>0}\times\tbinom At\bigr),\\
g(b)&=0,& f_b(a)&=0,\\
g(n,J)&=n,&
f_{(n,J)}(a)&=\begin{cases}0,&a\in J,\\ n,&a\notin J.\end{cases}
\end{aligned}
\tag{1.1}
$$

One actual $x\in X_{N,t}$ stays fixed throughout an execution.
The legal source action $\operatorname{Read}(a)$ returns $f_x(a)$ and
leaves $x$ unchanged. Every $a\in A$ is legal, including a repeated
address. Reading an address is an acquisition; a response at an unread
address is not supplied. There is no prior on $X_{N,t}$.
The address interface has no metric, and the order of actual actions is
an execution order without a supplied physical clock.

**Definition 1.2 (one common randomized policy).**
A policy uses a probability space $(\Theta,\mathcal F,\mu)$ whose law
is independent of the source. Fixing $\theta\in\Theta$ gives one
deterministic procedure. Its actions, internal transitions, stopping
and proposed upper bound depend only on public parameters, that tape
and previously acquired replies and retained control information.
In particular neither $n$, $J$ nor a source-dependent program is supplied.
All retained history, random choices and numerical values used by the
procedure are part of its information, rather than an extra advice port.

At source $x$, write $T_x$ for its number of execution transitions before
stopping, $h_x=((a_1,y_1),\ldots,(a_{R_x},y_{R_x}))$ for its ordered
acquired query record, and $C_x$ for its terminal proposed upper bound.
Internal transitions and the terminal transition also contribute to
$T_x$. The class $\mathcal P_s$ consists of policies such that, for every
fixed source, $T_x<\infty$ and $C_x\in\mathbb R$ almost surely, with
exactly one such terminal proposal. Each execution queries at most $s$
distinct addresses, where $0\le s\le N$. Repetitions and internal work
are allowed; neither a uniform execution horizon nor a uniform bound
on the finite values $C_x$ is imposed.

All finite execution records, stopping events and query sets are
measurable, using discrete fields for actions and integer responses and
Borel fields for real proposals. For each fixed source $x$, the
terminating domain $L_x$ is measurable and has full measure, and
$T_x,h_x,C_x$ are measurable there. On $\Theta\setminus L_x$ give them
the fixed defaults $+\infty$, the empty record and $0$, respectively.
These totalizations are measurable even when $(\Theta,\mathcal F,\mu)$ is
not complete, since each default is constant on a measurable set.
Any other measurable totalizations agreeing on $L_x$ give the same
probabilities below. The sourcewise error and worst-source error are

$$
e_x(P)=\mu\{C_x<g(x)\},\qquad
\mathcal E(P)=\sup_{x\in X_{N,t}}e_x(P),\qquad
V(N,t,s)=\inf_{P\in\mathcal P_s}\mathcal E(P).
\tag{1.2}
$$

Correctness here is correctness at the actual source. A finite proposal
need not bound the targets of every other source compatible with its
record. In particular $C_b<0$ is an error at $b$.

The common-tape, sourcewise-probability convention is the one in
[KBonacci Self Calibrating Boundaries, Definition 38.1](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md).
That definition concerns Boolean prime queries on a different source
space; (1.1) instead supplies exact numerical replies. Its source space
and numerical access are not supplied by a finite Boolean decision-tree
model.

**Definition 1.3 (separate acquisition charges).**
For a finite acquired record $h$, let $Q(h)$ be its set of distinct
addresses and let $R(h)$ be its length. The charges

$$
D(h)=|Q(h)|,\qquad R(h),\qquad
B(h)=\sum_{(a,y)\text{ in }h}\ell(y),\qquad
\ell(0)=1,\quad \ell(n)=1+\lfloor\log_2 n\rfloor\ (n>0)
\tag{1.3}
$$

measure distinct addresses, actual query calls and binary response
length, respectively. They are different from $T_x$, random-bit use,
working memory and the representation length of a proposal. Equation
(1.2) constrains only $D$. A numerical response $n$ has finite length
for each $n$, but no uniform length bound over the source space.
No uniform finite-bit implementation is part of $\mathcal P_s$.

## 2. Adaptive minimax risk and a fixed bad source

**Theorem 2.1 (the finite-address upper-proposal value).**
For every $0\le s\le t<N$,

$$
V(N,t,s)=p_{N,t,s}:=\frac{\binom ts}{\binom Ns}>0.
\tag{2.1}
$$

This value includes all adaptive policies of Definition 1.2 and all
almost-surely finite real proposal distributions, including unbounded
ones. For each such policy there is a single $J_*\in\binom At$ such
that

$$
\sup_{n\ge1}e_{(n,J_*)}(P)\ge p_{N,t,s}.
\tag{2.2}
$$

The infimum over policies is attained. The supremum over finite sources
in (2.2) need not be attained.

**Proof.** Run $P$ at $b$ and, on its full-measure set of finite runs,
put $Q(\theta)=Q(h_b(\theta))$, $q(\theta)=|Q(\theta)|$ and
$C(\theta)=C_b(\theta)$. For a fixed $J\in\binom At$ let

$$
E_J=\{\theta:T_b(\theta)<\infty,\ Q(\theta)\subseteq J\}.
\tag{2.3}
$$

On $E_J$, running the same policy with the very same tape at $(n,J)$
reproduces the entire baseline execution. Indeed the initial
information agrees. At every later transition, equal acquired histories
and equal tape give equal control decisions; each queried address lies
in $Q(\theta)\subseteq J$, so its reply is again zero. The stopping
decision, execution length, repeated reads and terminal output therefore
agree. This is the fixed-path passive transfer used by
[PassivePolicyNormalization, `execute_transfer`](../../../D5/S3/ConceptDynamics/Experiment/PassivePolicyNormalization.lean),
applied separately to each fixed tape and finite record. The probability
argument below is additional to that fixed-path statement.

A $q$-element query set is contained in exactly
$\binom{N-q}{t-q}$ members of $\binom At$. Finite summation and
integration consequently give

$$
\frac1{\binom Nt}\sum_{J\in\binom At}\mu(E_J)
 =\int_\Theta\frac{\binom{N-q(\theta)}{t-q(\theta)}}{\binom Nt}
       \,d\mu(\theta)
 \ge\frac{\binom{N-s}{t-s}}{\binom Nt}
 =\frac{\binom ts}{\binom Ns}.
\tag{2.4}
$$

Set the integrand to zero on the measurable null omitted set.
For $0\le q\le s$, its value is
$\prod_{i=0}^{q-1}(t-i)/(N-i)$; adding a factor in $[0,1]$ cannot
increase it. Empty products cover $s=0$, including $t=0$.
Thus some fixed $J_*$ has $\mu(E_{J_*})\ge p_{N,t,s}$.
For every positive integer $n$, the same-path comparison gives

$$
E_{J_*}\cap\{C<n\}\subseteq
 \{C_{(n,J_*)}<n\}.
\tag{2.5}
$$

Because $C$ is finite almost surely, the events on the left increase to
$E_{J_*}$ up to a null set as $n\to\infty$. Hence
$\sup_n e_{(n,J_*)}(P)\ge\mu(E_{J_*})\ge p_{N,t,s}$.
The set $J_*$ is selected before varying $n$ or quantifying over tapes;
$n$ is constant on each event in (2.5). No tape-dependent adversarial
source has been integrated as though it were one source.

For the matching policy, sample a uniform $s$-element set $S\subseteq A$
independently of the source, query its addresses in public increasing
order until the first positive reply or the end, output the positive
reply when there is one, and otherwise output zero. Every run has at
most $s$ calls. At $b$ the proposal is correct. At $(n,J)$ it is false
exactly when $S\subseteq J$, an event of probability
$\binom ts/\binom Ns$. Thus (2.1) holds, and this policy attains the
minimax value. The possible nonattainment over sources is proved in
Proposition 2.2. $\square$

The sampling probability in this proof is classical. In the
[R hypergeometric manual, Details](https://stat.ethz.ch/R-manual/R-devel/library/stats/html/Hypergeometric.html),
take population counts $m=t$, $n=N-t$, sample size $k=s$ and sampled
success count $x=s$. The same uniform-subset counting convention is
stated in [Random Services, Hypergeometric Distribution, The Probability
Density Function](https://www.randomservices.org/random/urn/Hypergeometric.html).
These are suppliers for (2.4) and the matching sampling policy, not a
claim that sampling without replacement is new. The source-relative
combination here includes the unbounded integer target, adaptive acquired
zero paths and the exhaustion by finite real proposals. It is a
`repo-derived` deduction; no literature-priority assertion is made.

**Proposition 2.2 (attainment and nonattainment are different).**
The policy in Theorem 2.1 has error $p_{N,t,s}$ at every high source.
There is also a minimax policy with error strictly less than $p_{N,t,s}$
at every source, whose worst-source error is nevertheless $p_{N,t,s}$.

**Proof.** Retain the uniform subset $S$, but on the all-zero branch
output an independent integer $G\ge1$ with
$\Pr(G=m)=2^{-m}$. On a positive reply still output $n$. Then

$$
e_b=0,\qquad
e_{(n,J)}=p_{N,t,s}\Pr(G<n)
 =p_{N,t,s}\bigl(1-2^{-(n-1)}\bigr)<p_{N,t,s}.
\tag{2.6}
$$

Every $G$ is finite and $\Pr(G<n)\uparrow1$. Thus the supremum is
$p_{N,t,s}$ and is attained by no finite source. The unbounded finite
integer-output distribution is already used in
[KBonacci, Proposition 38.4](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md);
its use here separates the two notions of attainment for (2.1).
$\square$

## 3. Exact source fibres, batches and the limits of a target boundary

**Definition 3.1 (compatibility of acquired records).**
For a finite numerical query record $h$, set

$$
\mathcal C(h)=\{x\in X_{N,t}:f_x(a)=y
                   \text{ for every occurrence }(a,y)\text{ in }h\}.
\tag{3.1}
$$

This is a response fibre, without a probability prior. If $h$ is an
actual record of a policy on a fixed tape, every $x\in\mathcal C(h)$
reproduces that record, its intervening control transitions and its
stop/output decision whenever the original execution has stopped.
This follows from the finite-path transfer in Theorem 2.1, not from
supplying the fibre itself as an observation.
Let $Z(h)$ and $P(h)$ be the distinct addresses with zero and positive
replies, respectively. An actual record has consistent replies at
repeated addresses.

**Theorem 3.2 (fibres and exact recovery at a passive cut).**
If $h$ is all zero, with $z=|Z(h)|$, then

$$
\mathcal C(h)=\{b\}\ \sqcup\
 \{(n,J):n\ge1,\ |J|=t,\ Z(h)\subseteq J\}.
\tag{3.2}
$$

For $z\le t$ its compatible target values are exactly
$\{0,1,2,\ldots\}$; for $z>t$ its sole source is $b$.
If $h$ contains a positive reply, all its positive replies at a
compatible source must equal one integer $n\ge1$, and then

$$
\mathcal C(h)=\{(n,J):Z(h)\subseteq J\subseteq A\setminus P(h),\ |J|=t\}.
\tag{3.3}
$$

With $z=|Z(h)|$, $p=|P(h)|$ and disjoint $Z(h),P(h)$, this fibre has
$\binom{N-z-p}{t-z}$ elements, and is nonempty exactly when
$z\le t$ and $p\le N-t$. Inconsistent repeated replies, distinct
positive reply values, negative replies or noninteger positive replies
have empty fibre.

At a nonempty fibre, exact target recovery means assigning a value
correct for every compatible source; exact future-response recovery
means assigning the correct function $a\mapsto f_x(a)$ for every
compatible source. The latter also determines every future passive
query response under any acquired-history policy and fresh tape.
An all-zero record admits either recovery precisely when $z>t$.
A positive record always recovers the target $n$, but recovers the whole
future-response function precisely when

$$
z=t\quad\hbox{or}\quad p=N-t.
\tag{3.4}
$$

**Proof.** A zero reply at an address is equivalent to membership in
$J$ at a high source, and a positive reply equals $n$ and is equivalent
to nonmembership. The baseline supplies only zeros. These facts give
(3.2) and (3.3), including their consistency conditions. In (3.3),
choose the remaining $t-z$ zero addresses from the $N-z-p$ unread
addresses; this proves the count and the nonemptiness criterion.

The map $x\mapsto f_x$ is injective. Its all-zero function is unique to
$b$, because $t<N$. Any other function reveals $n$ at a positive
address and reveals $J$ as its zero set. Thus future-response recovery
holds exactly for singleton fibres. Equation (3.2) has one source
exactly when $z>t$; otherwise even $n$ is unrestricted. For (3.3),
write $u=N-z-p$ and $v=t-z$. A nonempty choice family of $v$-subsets
of a $u$-set is a singleton exactly when $v=0$ or $v=u$. If
$0<v<u$, swap one chosen and one unchosen unread address to obtain
two different compatible sources with different next replies at those
addresses. This gives (3.4). The response function, combined with the
specified policy and tape, determines future records and stopping by
successive evaluation; it does not reveal unretained earlier history.
$\square$

The record-fibre test is an application of
[Boundary Dynamics, Theorem 2.1 and Corollary 2.2](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md):
a proposed boundary must preserve the outputs and legal successors
required by the selected future experiments. It does not promote an
uncertain candidate set to the actual response function. Likewise
[Process Geometry, Proposition 43.1](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)
qualifies §39.2: mutual recovery of supplied views and task sufficiency
give a common kernel contained in the task kernel; identifying that
kernel with the task kernel additionally requires nonredundancy.
No additional general quotient criterion is needed here.

**Theorem 3.3 (one source for a batch of zero executions).**
Let $(h_i)_{i\in I}$ be any nonempty collection of actual finite
all-zero executions, with their individual fixed tapes and policies
satisfying Definition 1.2. Write $Q_i=Q(h_i)$ and
$U=\bigcup_{i\in I}Q_i$. There is one high source $(n,J)$ reproducing
every one of these executions on its respective tape if and only if

$$
|U|\le t.
\tag{3.5}
$$

If these executions terminate in finite real proposals $C_i$, one high
source can both reproduce all of them and falsify all proposals if and
only if $|U|\le t$ and $\sup_{i\in I}C_i<\infty$. For a finite batch,
the second condition is automatic.

**Proof.** A matching high source must have $Q_i\subseteq J$ for every
$i$, hence $U\subseteq J$ and $|U|\le t$. Conversely extend $U$ to a
$t$-subset $J$ of $A$. Each $n\ge1$ gives all the required zero replies;
finite-path transfer preserves each individual execution. For falsity
also require $n>C_i$ for all $i$. Such a positive integer exists exactly
when the real proposals are bounded above. Necessity follows from
$\sup_i C_i\le n$ for any witnessing integer. $\square$

For a measurable tape event $E$ at $b$, literal matching on every tape
requires (3.5) for the union of its query sets. Matching almost surely
on $E$ instead requires one fixed $J$ with
$\mu(E\setminus E_J)=0$. Individual existence of a compatible $J$
on each tape proves neither statement. These are the explicit batch
conditions behind the counting step of (2.4).
[KBonacci, Theorem 38.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md)
already chooses one source for an entire truncated event; its finite
prime-cylinder supplier has a different compatibility capacity from
(3.5).

**Proposition 3.4 (the two-address separation).**
For $N=2$, $t=s=1$, choose each address with probability $1/2$, query
it and output its reply. Every individual zero execution has high
compatible sources of arbitrarily large target, but no high source
matches both zero executions. The policy has worst-source error $1/2$.
Thus unbounded target in every individually acquired zero fibre does
not force worst-source error one.

**Proof.** A zero at address $a$ is compatible with every $(n,\{a\})$.
The two executions together query $\{1,2\}$, violating (3.5).
For a fixed $(n,J)$, exactly one address gives zero and the other gives
$n$, so its error probability is $1/2$. The baseline error is zero.
Theorem 2.1 shows that this risk is optimal. $\square$

**Corollary 3.5 (the zero-error acquisition threshold).**
The least worst-execution number of distinct addresses allowing an
almost-surely finite upper proposal with zero error at every source is
$t+1$. The same threshold holds for exact target output.

**Proof.** For any bound $s\le t$, Theorem 2.1 gives positive worst-source
error. For $s=t+1$, query $t+1$ distinct addresses until the first
positive reply, outputting that reply, or output zero if all replies
are zero. A high source has only $t$ zero addresses, so its target is
encountered; an all-zero record certifies $b$ by (3.2). This terminates
on every tape and source with the exact target. $\square$

**Proposition 3.6 (future response and chronology require different data).**
Exact target recovery, full future-response recovery and recovery of
acquired chronology are distinct tasks in (1.1). In particular a target
boundary need not support the next unread response, and even a complete
response function need not recover the order or cost of its past
acquisition.

**Proof.** Take $N=3,t=1$ and the positive one-read record $((1,n))$.
The sources $(n,\{2\})$ and $(n,\{3\})$ have this record and the same
target $n$, but their next replies at address 2 differ. This consumes
the strict part of (3.4).

At $b$ with $N\ge2$, the histories $((1,0),(2,0))$ and
$((2,0),(1,0))$ have the same response function, acquired set and number
of calls, but different chronology. With $N=2,t=1$, both already
identify $b$. The histories $((1,0),(2,0))$ and
$((1,0),(1,0),(2,0))$ in that same family also identify $b$ and have
the same distinct-query charge, but their query-call and response-bit
charges are 2 and 3. These are actual legal histories, obtainable by
public deterministic schedules. Recovering their past order or call
count requires retention of additional acquired data. Neither response
recovery nor set compatibility supplies such retention. $\square$

## 4. Deleting an actually acquired fixed zero prefix

**Definition 4.1 (the fixed-prefix continuation task).**
Fix a public ordered list of $k$ distinct addresses, $0\le k\le t$,
with set $K\subseteq A$. Actually execute those $k$ reads and retain
their all-zero record $h_K$. The original source is then in

$$
X_K=\{b\}\sqcup\{(n,J):K\subseteq J,\ |J|=t,\ n\ge1\}.
\tag{4.1}
$$

It is not redrawn from this set. Continuations may read addresses in
$U=A\setminus K$ and use independent, source-independent fresh
randomness. They use one common program with public $K,h_K$ and their
own acquired continuation records; neither the original hidden source
nor extra information about it is supplied. Their initial retained
configuration is the same at every member of $X_K$.
The continuation task has no access to a source-correlated prefix tape.
It counts at most $r$ distinct new addresses per execution, terminates
and produces a finite real proposal almost surely at every original
source in $X_K$, and tests that proposal against the original $g(x)$.

Reads of $K$ are not allowed in this remaining-address interface.
A different interface that permits such repeated reads must charge
those calls; obtaining their known zero values from retained memory is
not an actual query. The prefix already has charges $D=R=B=k$.
Its execution transitions and memory are also retained in the total
accounting.

**Theorem 4.2 (exact residual source correspondence).**
Let $\varphi:\{1,\ldots,N-k\}\to U$ be a public bijection. The map

$$
\Psi(b)=b,\qquad
\Psi(n,J)=\bigl(n,\varphi^{-1}(J\setminus K)\bigr)
\tag{4.2}
$$

is a bijection from $X_K$ to $X_{N-k,t-k}$. It preserves the target.
Under the address identification $\varphi$, the two continuation
problems have exactly the same legal responses, ordered continuation
records, stopping decisions, outputs and continuation charges on each
tape. Every policy in either problem transports to a policy in the
other with those properties. For $0\le r\le t-k$, the continuation
minimax error is therefore

$$
V_K(r)=\frac{\binom{t-k}{r}}{\binom{N-k}{r}}.
\tag{4.3}
$$

For $t-k+1\le r\le N-k$, it is zero. The least zero-error number of
new distinct queries is $t-k+1$, and the total threshold including
acquisition is $k+(t-k+1)=t+1$.

**Proof.** The inverse of (4.2) sends $(n,J')$ to
$(n,K\cup\varphi(J'))$; the two pieces are disjoint and have total
cardinality $t$. Both maps leave the same numerical target $n$ intact,
and send the baseline to the baseline. For each remaining address $i$,

$$
f_x(\varphi(i))=f_{\Psi(x)}(i).
\tag{4.4}
$$

Translate each query using $\varphi$, retain the same tape and all
control rules, and append the public fixed prefix when interpreting
an original record. Induction on actual transitions using (4.4) gives
equal replies and decisions, including repeats of remaining addresses,
internal work, stopping and output. Conversely remove that fixed prefix
and use $\varphi^{-1}$. The fixed initialized state and independent
continuation randomness ensure that this inverse introduces no hidden
advice or source-dependent tape law.

The bijection preserves the number of distinct continuation addresses,
number of actual continuation calls and every numerical reply length.
It also preserves the declared continuation transitions. In original
coordinates these costs add to the already incurred prefix costs;
in particular $D_{\rm total}=k+D_{\rm continuation}$ and
$R_{\rm total}=k+R_{\rm continuation}$. The image source in (4.2) is a
coordinate description of the same fixed original source, not a reset.
Thus the two sourcewise error families and admissible policy classes
correspond. Apply Theorem 2.1 and Corollary 3.5 to obtain (4.3) and the
thresholds. The same correspondence transports the fibres of Theorem
3.2 and hence both its target and full future-response recovery tests.
$\square$

**Proposition 4.3 (conditioning on acquisition can change the tape law).**
A source-independent random prefix need not retain a source-independent
tape distribution conditional on acquiring zeros. Any subsequent error
claim restricted to that acquisition event must retain its sourcewise
probability.

**Proof.** In $X_{2,1}$ let a fair prefix tape select one address $A_1$,
perform that read and let $E$ be the event that its reply is zero.
Then

$$
\Pr_b(E)=1,\qquad
\Pr_{(n,\{1\})}(E)=\tfrac12,
\tag{4.5}
$$

and

$$
\Pr_b(A_1=1\mid E)=\tfrac12,\qquad
\Pr_{(n,\{1\})}(A_1=1\mid E)=1.
\tag{4.6}
$$

Thus the conditioned prefix tape laws differ although their original
laws agree. Independent fresh continuation randomness retains its law,
but does not undo this selection of the prefix information. For any
subsequent error event $F$ and fixed source with $\Pr_x(E)>0$,

$$
\Pr_x(F\cap E)=\Pr_x(E)\Pr_x(F\mid E).
\tag{4.7}
$$

If $\Pr_x(E)=0$, the left side is zero and no conditional claim is
assigned. An unconditional sourcewise bound $\Pr_x(F)\le\delta$
therefore bounds the conditional probability by at most
$\min\{1,\delta/\Pr_x(E)\}$, not automatically by $\delta$.
Equations (4.5)–(4.7) preclude replacing a random acquired prefix by a
free fixed prefix without checking its conditional information and
acquisition mass. $\square$

## 5. Actual retry, a fixed latent source and uniform recovery

**Definition 5.1 (source, active state and attempt outcome).**
For active examples, a configuration has an immutable source $x$ and
a mutable state $z$. A legal action may change $z$, permissions and
retained memory, but source-preserving actions leave $x$ fixed.
An attempt begins at a designated ready state and has one of the
following mutually exclusive outcomes: $H$, a finite real proposal;
$R$, a finite termination without a proposal; or $D$, literal infinite
execution without termination. The false proposals form $F\subseteq H$,
with probabilities $h_x,r_x,d_x,e_x$ and
$r_x=1-h_x-d_x$. A finite unknown, abort or infinite-valued output is
not $D$.

A retry instruction means that after an $R$ outcome the controller
tries to continue. It grants no reset action, lost permission or new
source. A reset, when allowed, is a specified legal operation with
specified state effects, observable failures and costs. Each attempt
start and each recovery action contributes at least one execution
transition; infinitely many finite retries therefore form an infinite
execution. The numerical queries of Sections 1–4 are passive and need
no state restoration; the active examples below have their own declared
interfaces.

**Proposition 5.2 (two active states defeat a fresh-tape restart).**
There is a source-preserving two-state system with initial attempt
probabilities $h=1/2,d=0,r=1/2$, in which repeatedly attempting after a
finite nonproposal gives eventual proposal probability $1/2$, rather
than $h/(h+d)=1$. Independent fresh randomness for each attempt does
not change this fact.

**Proof.** Take a singleton source with target 1, states $u$ and $v$,
and initial state $u$. Both states permit the action Attempt. At $u$,
it consumes one fair independent bit, changes the state to $v$, and
returns either the proposal 1 or the finite label retry, each with
probability $1/2$. At $v$, Attempt performs an endless sequence of
internal transitions and never returns. There are no other actions.
Every source action leaves the singleton source unchanged.

The initial attempt has exactly the probabilities asserted. On its
proposal branch the controller stops. On its retry branch it remains
at $v$, where the second attempt diverges with probability one. Thus
the actual eventual proposal and divergence probabilities are both
$1/2$. The state $u$ cannot be restored by any legal action.

There is a second version with the same initial probabilities: replace
the action at $v$ by a finite return of retry, leaving $v$ unchanged.
After an initial retry every individual attempt is now finite, yet the
controller makes infinitely many of them and still never proposes.
The full execution again diverges on a set of probability $1/2$.
The first version traps inside one attempt; the second accumulates
infinitely many finite nonproposals and attempt-start charges. Neither
version authorizes identifying a finite nonproposal with literal
divergence of that individual attempt. $\square$

**Proposition 5.3 (a source drawn once cannot be reaveraged at each retry).**
Even when the attempt law regenerates at each fixed source, the ratio
of prior-averaged attempt probabilities need not be the actual eventual
proposal probability under that prior.

**Proof.** Draw $x=A$ or $x=B$ once with equal probabilities, then keep
it fixed. Give both sources target 1. At $A$, each attempt immediately
proposes 1. At $B$, each attempt uses a new independent fair bit to
diverge literally with probability $1/2$ or to return a finite retry
with probability $1/2$. After a finite retry the same source is ready
for the next attempt without any further state change. The private
bits are independent of the initial source draw.

The prior-averaged first-attempt probabilities are

$$
\bar h=\tfrac12,\qquad\bar d=\tfrac14,\qquad\bar r=\tfrac14,
\qquad \frac{\bar h}{\bar h+\bar d}=\tfrac23.
\tag{5.1}
$$

At $A$ a proposal occurs immediately. At $B$ no attempt can propose;
the probability of $m$ consecutive finite retries is $2^{-m}$, so
literal divergence in some attempt has probability one. Hence

$$
\Pr(\text{eventual proposal})=\tfrac12,
\qquad
\Pr(\text{eventual divergence})=\tfrac12.
\tag{5.2}
$$

Reaching a second attempt has prior probability $1/4$ and identifies
$x=B$, where the conditional proposal probability is zero. It is
therefore false that each reached attempt has proposal probability
$\bar h$. Conditional on each original source the established scalar
calculation gives 1 at $A$ and 0 at $B$; averaging these completed
sourcewise probabilities gives (5.2). Drawing a new source at each
retry would define a different experiment. $\square$

**Definition 5.4 (one acquired-information recovery strategy).**
At a returned record $a$, let $\mathcal K(a)$ be the set of original
source/current-state pairs $(x,z)$ compatible with that actual acquired
information and the preceding legal operations. Compatibility retains
both the original source identity and the current state; it is not the
Cartesian product of separately possible coordinates.
A recovery strategy is one common measurable policy that chooses
operations from its acquired information, retained working state and
fresh source-independent randomness. It must operate legally and meet
its stated success condition for every $(x,z)\in\mathcal K(a)$,
sourcewise almost surely. The policy cannot be separately selected
using an unobserved pair $(x,z)$. All observations, state changes,
recovery failures, elapsed transitions and acquisition charges belong
to its execution.

**Proposition 5.5 (pairwise available resets need not give a recovery strategy).**
There are two compatible hidden sources for which each individually
has a successful legal reset, but no acquired-information strategy
succeeds almost surely at both. The best worst-source success
probability is $1/2$.

**Proof.** Let the original source be $x\in\{0,1\}$. Both sources
have the same acquired record and the same observed spent state.
The only actions are the two reset buttons $a_0,a_1$; both are legal
and each costs one transition. At source $x$, pressing $a_x$ returns
the ready state with success. Pressing the other button halts with a
finite failure and grants no further action. Before pressing a button
there is no observation that depends on $x$. Both buttons preserve the
original source, including on failure.

Let $p_i$ be the source-independent probability that a proposed
strategy's first button is $a_i$; a strategy that never presses either
button contributes to neither success event. Thus $p_0+p_1\le1$,
and the two sourcewise success probabilities are $p_0,p_1$.
Their minimum is at most $1/2$, attained by a fair one-button choice.
Each hidden source has its own successful button, but the quantifiers
$\forall x\,\exists a_x$ cannot be replaced by one strategy based on
the common record. $\square$

## 6. The regeneration obligation for scalar restart calculations

**Assumption 6.1 (legal sourcewise conditional regeneration).**
Fix a reference attempt for each original source $x$, with scalar
probabilities $(h_x,e_x,d_x,r_x)$ as in Definition 5.1. The actual
controller starts that attempt and stops on its first proposal. After
every finite nonproposal it uses a strategy of Definition 5.4.
For every compatible original-source/current-state pair this same
strategy preserves $x$ and returns legally to a ready configuration
after finite execution almost surely, without itself issuing a terminal
proposal. After return it restores the reference scalar law for the
next attempt, including conditional on acquired recovery information.
This success condition is required for every compatible pair, not only
after averaging over unobserved current states. Its working memory and
all reset operations have the declared access and costs. There are no
unaccounted finite failures or divergent recoveries.

For each fixed $x$, let $A_j$ be the event of reaching the $j$th attempt,
and let $\mathcal F_j$ contain the complete actual history just before
that attempt, including acquisition, prior outcomes and recoveries.
On $A_j$, conditional on $\mathcal F_j$, its probabilities of the four
outcome classes $F,H\setminus F,D,R$ are, almost surely,

$$
(e_x,\ h_x-e_x,\ d_x,\ r_x).
\tag{6.1}
$$

Here $A_1$ is certain. The conditional statement can equivalently be
written as conditional-expectation identities with a factor
$\mathbf1_{A_j}$, so no conditioning on an individual null history is
required. The legal uniform recovery requirement is pointwise over
compatible pairs; (6.1) is a sourcewise probabilistic requirement on
actual reached histories. Fresh independent attempt randomness and
restoration of a state with the reference scalar response law are one
sufficient way to establish (6.1). Fresh randomness alone is not that
restoration.

The regeneration hypothesis concerns conditional laws at actual cuts.
[Finite Start Predictive Memory, Assumption 10.1 and Definition 11.1](RECURSIVE_RELATIONAL_OBSERVATION_FINITE_START_PREDICTIVE_MEMORY.md)
separates one fixed source, authentic calibration and acquired updates
from supplied forecast coherence. An authentic label must not replace
the source or trajectory. Likewise
[Stopped Episode Calibration Unidentifiability, Definition 3.1 and
Proposition 4.2](RECURSIVE_RELATIONAL_OBSERVATION_STOPPED_EPISODE_CALIBRATION_UNIDENTIFIABILITY.md)
uses one original episode without reset or post-Stop access; its
supplied candidate generator is not a source operation. Neither contract
supplies Assumption 6.1 for a new active system.

**Proposition 6.3 (reset failure and cumulative charges in the two-state example).**
Augment the first system of Proposition 5.2 by a legal Reset action at
$v$. Every such action costs one call. Independently on each invocation,
it restores $u$ with probability $\alpha\in[0,1]$ and otherwise halts
with finite abort. Each Attempt at $u$ also costs one call and uses an
independent fair bit. The controller stops on a proposal or abort and,
after a retry, uses Reset before its next attempt. At $\alpha=1$ this
actual recovery meets Assumption 6.1; at $\alpha<1$ it does not.
Accounting for the actual reset outcomes, its probabilities are

$$
\Pr(\text{proposal})=\frac1{2-\alpha},\qquad
\Pr(\text{finite abort})=\frac{1-\alpha}{2-\alpha},\qquad
\Pr(\text{divergence})=0.
\tag{6.3}
$$

Its expected counts of Attempt and Reset calls are respectively
$2/(2-\alpha)$ and $1/(2-\alpha)$. For every $\alpha>0$ it has no
finite worst-execution call bound. If unsuccessful Reset instead
literally diverges, the same mass $(1-\alpha)/(2-\alpha)$ is divergence
rather than finite abort; the expected number of initiated calls stays
the same, whereas infinite internal execution is then possible.

**Proof.** The scalar supplier is
[KBonacci, Corollary 39.2, equation (39.3)](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md),
including its disjoint-attempt calculation and zero-denominator case.
To apply it to actual recovery under Assumption 6.1, fix one original
source $x$. Removing each finite recovery segment preserves the
attempt outcome and false-proposal labels, and every reached $R$ is
followed legally by another attempt at that same $x$. By (6.1) and
iterated conditional expectation, every finite string of retry outcomes
followed by a proposal or divergence has the same probability as in
the supplier's reference restart experiment. This verifies the
correspondence needed for its scalar calculation; independence of
complete attempt records is stronger than required. Countably many
sourcewise null recovery failures remain null for each fixed $x$.
Thus the credited identities used for this comparison are

$$
\widetilde h_x=\frac{h_x}{h_x+d_x},\qquad
\widetilde e_x=\frac{e_x}{h_x+d_x}
\quad\text{if }h_x+d_x>0,
\tag{6.2}
$$

with both zero when $h_x+d_x=0$. When the denominator is positive,
the supplier's calculation gives zero mass to infinitely many returned
retries, leaving nonproposal mass $d_x/(h_x+d_x)$ as literal divergence
in an attempt. When it is zero, every reached attempt returns $R$
almost surely and the actual controller makes infinitely many attempts
almost surely. The positive transition charge of every restart makes
this literal divergence of the full execution, even though each
attempt and recovery is finite almost surely. These are sourcewise
comparisons and do not replace $x$ by a prior mixture.

In the present two-state system, $\alpha=1$ supplies legal finite
restoration of $u$ after each retry and the independent fair attempt
bit supplies (6.1), with $(h,e,d,r)=(1/2,0,0,1/2)$. Equation (6.2)
therefore gives proposal probability 1 and false-proposal probability
zero, with no divergence. The reset calls still carry their own costs.
For $\alpha<1$ a reached reset fails with positive probability, so this
application of Assumption 6.1 is unavailable.

For every $\alpha\in[0,1]$, the chance of reaching attempt $j$ in the
actual system is $(\alpha/2)^{j-1}$: reaching another ready attempt
requires both a retry and a successful reset. Thus endless returned
retries have probability $\lim_m(\alpha/2)^m=0$. Let $p$ and $a$ be
the actual eventual proposal and finite-abort probabilities. Conditioning
on the first Attempt and its possible Reset gives

$$
p=\tfrac12+\tfrac\alpha2p,\qquad
a=\tfrac{1-\alpha}{2}+\tfrac\alpha2a.
$$

Solving these two equations proves (6.3). Let $M$ and $G$ be the
expected counts of initiated Attempt and Reset calls. The above
reach probabilities are at most $2^{1-j}$, so both expectations are
finite. Conditioning on the same first step then gives

$$
M=1+\tfrac\alpha2M,\qquad
G=\tfrac12+\tfrac\alpha2G,
$$

hence $M=2/(2-\alpha)$ and $G=1/(2-\alpha)$.

For $\alpha>0$, the first $m$ attempts can all return retry and be
successfully reset, an event of positive probability $(\alpha/2)^m$;
the total count then exceeds every prescribed finite bound for a
suitable $m$. When reset failure is divergence, only its terminal type
changes, so the same event probabilities and initiated-call counts
apply. Internal transition time on that event is infinite. In
particular $\alpha<1$ fails the almost-sure finite recovery hypothesis
of Assumption 6.1 and cannot be silently treated as $\alpha=1$.
$\square$

**Proposition 6.4 (per-attempt budgets do not become total budgets).**
Even a legal passive retry using independent randomness does not
preserve a per-attempt distinct-query limit as a bound on the whole
repeated execution. Repeated acquisitions, numerical reply lengths and
recovery operations retain their own cumulative charges.

**Proof.** In $X_{2,1}$, let each attempt choose a fair address, read it,
propose its reply if positive, and otherwise return retry. The original
source remains unchanged. Each attempt has at most one distinct query.
At $b$ every attempt returns retry, so the full execution is infinite.
Its first two addresses are different with probability $1/2$, giving
total distinct-query charge 2 already on that finite prefix. Its call
count and response-bit charge grow without bound with the attempt
count. At a high source each attempt has proposal probability $1/2$;
repetition eventually finds $n$ almost surely, but it also permits two
distinct queried addresses. It consequently lies outside the
one-distinct-query class of Theorem 2.1 and fails its baseline finite
termination requirement. There is no contradiction to the minimax
bound. Costs of each actual reset or internal transition add in exactly
the same way; only repeated addresses can overlap in the distinct-set
count. $\square$

## 7. Which recovery relation is actually supplied

**Definition 7.1 (four different comparison contracts).**
Fix an original source and a reference ready configuration. The
comparison with a recovered configuration can require any of the
following, with the observation interface specified in each case.
Scalar attempt-law recovery is equality of the four probabilities in
(6.1). Full future-law recovery is equality of the joint laws of all
declared future records, outputs, legality and failure labels, stopping
types and charges for each allowed continuation. Same-tape transport
requires equality of those actual future executions for every common
tape in the declared comparison domain, rather than only equality in
law. Literal restoration requires an actual legal operation ending in
the specified original configuration, including its declared source,
permissions, control and memory fields.

Literal restoration of only a projected state label is weaker than
literal restoration of a complete configuration. An append-only archive
cannot be erased merely by calling an operation a reset. When only an
attempt-local working component is restored, the retained older archive
and cumulative charges stay in the complete state and must be accounted
for in the selected comparison. A complete-state restoration together
with the original conditional future transition law and independent
fresh randomness suffices for full future-law recovery. The conditional
law assumption includes any environment or hidden mechanism capable
of changing that future.

**Proposition 7.2 (strict separations of the comparison contracts).**
Scalar attempt-law recovery does not imply full future-law recovery;
full future-law recovery does not imply same-tape transport; and
same-tape transport of every allowed future does not imply a legal
literal restoration.

**Proof.** For the first assertion, take target 1 and one permitted
terminal action. At the reference configuration it outputs 1, and at
the current configuration it outputs 2. Both are certain finite
correct proposals with $(h,e,d,r)=(1,0,0,0)$, but their real-output laws
differ. Source identity, permissions and the unit action cost are the
same.

For the second assertion, use a fair tape bit $U\in\{0,1\}$ and let
the sole terminal action output $1+U$ at one configuration and $2-U$ at
the other. The complete observable future in each case is one legal
unit-cost action with a uniformly distributed proposal in $\{1,2\}$.
Those laws agree, but the outputs differ on each common tape. The
complementary-tape coupling is not the asserted identical-tape
comparison.

For the third assertion, take states $z_0,z_1$ with the same immutable
source and a single action Read. In either state it returns zero at
unit cost and leaves that state fixed. Give the controller identical
retained information and permissions at both states. Every allowed
finite or infinite sequence, and every source-independent adaptive
choice of when to stop, has identical observable records, stopping and
costs on the same tape. Yet no legal action takes $z_1$ to $z_0$.
The full-future interface here excludes the hidden literal state label;
if that label is itself a required observable output, this example no
longer has full future-law equality. $\square$

The fresh-suffix result
[FreshServiceRestart, `first_acceptance_restart`](../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FreshServiceRestart.lean)
states that for iid coordinates and a positive-probability measurable
acceptance set, first acceptance leaves an independent untouched suffix
with its original product law. This supplies fresh service randomness,
not restoration of an actively changed source configuration or
permission. The iid cycle-pair assumption in
[Random Services, Renewal Reward Processes, Preliminaries](https://www.randomservices.org/random/renewal/Reward.html)
is likewise a substantive hypothesis; no renewal-reward theorem is
needed for (6.2), and no such theorem authorizes replacement of the
fixed latent source in Proposition 5.3.

**Proposition 7.3 (the scope of the two probability transfers).**
For the family (1.1), fixed-source batch compatibility and legal
source-preserving regeneration are different obligations. The former
is controlled by (3.5); the latter concerns an actual sequence of
states and acquired information. The scalar identities (6.2) alone
do not transport a finite-execution indistinguishability argument from
one source to another, nor do they identify a target boundary with a
complete past-and-future boundary.

**Proof.** Theorem 3.3 fixes one high source before replaying a whole
collection of baseline executions; Proposition 3.4 shows that choosing
one compatible source separately for each tape loses this property.
Theorem 4.2 preserves the original source by an explicit bijection on
its actually acquired fixed-prefix fibre and preserves its remaining
response interface. In contrast Proposition 5.2 keeps even a singleton
original source fixed while failing state regeneration, and Proposition
5.5 prevents an omniscient per-pair repair from defining an acquired
recovery policy.

Equation (6.1) retains only four conditional outcome probabilities.
The first two examples of Proposition 7.2 show that it does not supply
equality of numerical records or same-tape executions. Consequently
(6.2) cannot by itself justify an inclusion of a whole execution event
at one source in a false-output event at a second source, as required
in (2.5) or in KBonacci Theorem 38.2. Such an application must also
verify the actual records, legal recovery transitions, output and
stopping transport under one common source choice and tape law, with
the total costs belonging to the permitted policy class. Finally,
Proposition 3.6 gives actual histories with the same recovered future
response but different past chronology and charges, as well as equal
targets with different unread responses. Those counterexamples exclude
the asserted identifications without adding a generic quotient theorem.
$\square$

## 追加锚（本行以下为增补区）
