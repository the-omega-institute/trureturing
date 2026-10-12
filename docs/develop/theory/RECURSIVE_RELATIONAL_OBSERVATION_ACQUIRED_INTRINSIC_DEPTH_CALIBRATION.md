# Acquired calibration of intrinsic depth on every native tree

> This volume is reference input with ordinary mathematical proofs. Lean
> declarations and their accepted axiom closures remain the mathematical
> source of truth in the repository. The locator convention is `generic-v1`.
> After integration, existing bytes are preserved; corrections and extensions
> belong after the final append anchor. The results here have not been
> checked by the Lean kernel.

## 1. The continuation task and its owning results

The target is the intrinsic inverse-generation depth of a current tree after
an unknown nonnegative forward lag. Preparation actually acquires the original
tree. A separately supplied complete cut retains a calibration label and
isolates the remaining preparation information. Later the consumer reads only
the current right spine, using the original four-reply address interface.

Two existing advancing coordinates are used together: the right-spine
coordinate $c$ from [CLOCK] and [TM, §23][TM], and the intrinsic depth $\nu$ from
[JM, §36][JM]. Their difference is the right-spine coordinate of the unique
primitive endpoint. The content of this volume is the source-specific
calibration obstruction: **unknown forward lags can make the entire permitted
later observation identical while leaving different intrinsic depths**.
That obstruction makes the retained difference necessary even for labels
computed from the full prepared tree. Retaining that difference also gives an
effective consumer, its sourcewise read bounds, and a sharp calibration
alphabet on every defect-bounded domain.

This task differs from both complete current-tree acquisition and the
construction-context task of [JM, §§49–50][JM]. Complete acquisition already
recovers the tree, its geometry and $\nu$. The pair $Q=(\nu,e)$ already supplies
the exact construction-context quotient for depth. Neither result is claimed
as new here. The consumer below internally obtains $Q$ under the specified
retention and observation contract; it receives no $Q$, clock value, event
count or tree description at its later entry.

The original-address interface still permits every finite address. Restricting
the exhibited consumer and its calibration competitors to right-spine reads
is a task restriction, not a deletion of other legal source operations.
Section 7 explains why its lower bound cannot be extended to readers that
reacquire the complete tree.

## 2. Native sources, primitive rays and the supplied right-spine coordinate

**Definition 2.1 (all original ordered trees and literal reads).** Let

$$
\mathcal T::=\alpha\mid\beta\mid(s,t),\qquad
\rho\alpha=\beta,\quad \rho\beta=(\beta,\alpha),\quad
\rho(s,t)=(\rho s,\rho t).
\tag{IDC.2.1}
$$

The domain contains all nonempty finite free ordered full binary trees.
There is no identification of brackets, left and right, or equal labelled
occurrences, and no common bound on word, size, shape or intrinsic depth.
The address alphabet is $\Sigma=\{L,R\}$; its empty word $\varepsilon$ is the
root. For $y\in\mathcal T$, every finite word $q$ is a legal
$\mathsf{Read}(q)$ request. Its authentic reply $r_y(q)$ is
$\alpha,\beta,\mathsf{br}$ or $\mathsf{abs}$ according as the addressed
constructor is an alpha leaf, a beta leaf, a pair or absent. A nonempty
suffix below a leaf is absent. Pairing and $\rho$ describe mathematical
sources; they are not source operations granted to this consumer.

Write $\ell(u)$ for the number of leaves and $\mathsf{Addr}(u)$ for all
actually present node addresses. The length $|q|$ counts literal letters
in a submitted address, rather than bits in an index describing that word.
The right-spine subinterface consists exactly of the requests
$\mathsf{Read}(R^j)$, $j\in\mathbb N_0$, including $j=0$.

**Reuse 2.2 (unique primitive-ray decomposition and effective parsing).**
The exact supplier is [JM, Reuse 36.2 and Theorem 36.3][JM]. Put

$$
I_1=\rho[\mathcal T],\qquad \mathcal P=\mathcal T\setminus I_1.
$$

Every $u\in\mathcal T$ has a unique decomposition

$$
u=\rho^{\nu(u)}p(u),\qquad p(u)\in\mathcal P,
\qquad \nu(u)=\max\{n\ge0:u\in\rho^n[\mathcal T]\}.
\tag{IDC.2.2}
$$

In particular, for every $k\ge0$,

$$
p(\rho^k u)=p(u),\qquad \nu(\rho^k u)=\nu(u)+k.
\tag{IDC.2.3}
$$

The effective representation is a complete finite native tree description.
One-step image parsing uses the disjoint cases

$$
I_1::=\beta\mid(\beta,\alpha)\mid(I_1,I_1).
\tag{IDC.2.4}
$$

The inverse sends these cases respectively to $\alpha$, $\beta$, and the
pair of the two parsed inverses. The special pair is disjoint from the
last case because $\alpha\notin I_1$. Image membership and the inverse
on its domain are decidable by finite subtree recursion. Repeating the
existing inverse until image membership fails computes $p(u),\nu(u)$;
[JM, §36][JM] supplies termination and uniqueness, and [JM, §65.1][JM] explicitly
uses this finite computation. This is computation on an acquired description,
not inverse action on the source or an unexplained termination oracle.

**Definition 2.3 (right-spine coordinate and calibrated defect).** Use the
existing `rightClock` with the exact recurrence

$$
c(\alpha)=0,\qquad c(\beta)=1,\qquad c((s,t))=2+c(t).
\tag{IDC.2.5}
$$

If the rightmost leaf has depth $h$ and label bit $b$, with $b=0$ for
$\alpha$ and $b=1$ for $\beta$, then $c(u)=2h+b$.
Initially regard the subtraction in

$$
d(u)=c(u)-\nu(u)
\tag{IDC.2.6}
$$

as integer subtraction. Theorem 3.1 proves that it is nonnegative.
Use [JM, Definition 49.1][JM]'s original flag and pair:

$$
e(u)=\mathbf1_{\{p(u)=\alpha\}},\qquad Q(u)=(\nu(u),e(u)).
\tag{IDC.2.7}
$$

The coordinate $c$ is unrelated to the composition vector also denoted by
$c$ in some owning volumes.

**Reuse 2.4 (exact advancement and the four replies).** For every
$u\in\mathcal T$, $k,j\in\mathbb N_0$, the existing suppliers give

$$
c(\rho^k u)=c(u)+k,
\tag{IDC.2.8}
$$

$$
\begin{array}{c|c}
\text{reply at }R^j&\text{equivalent condition on }c(u)\\\hline
\mathsf{abs}&c(u)<2j\\
\alpha&c(u)=2j\\
\beta&c(u)=2j+1\\
\mathsf{br}&2j+2\le c(u).
\end{array}
\tag{IDC.2.9}
$$

These are [CLOCK]'s `right_clock_iterate` and `right_clock_readout`, with
the private `clock_step` as an existing proof supplier, and [TM,
(RA.2304), (RA.2307)][TM]. Under the literal source identification,
$\alpha=\mathtt{of\ true}$, $\beta=\mathtt{of\ false}$, pairing is
`FreeMagma.mul`, $\rho$ is `substitution`, and $R$ is the address bit
`true`; `rights j` is precisely $R^j$. No current clock value is delivered
by a new port. Formula (IDC.2.9) describes what an actual raw read means.

## 3. The stationary primitive calibration and its exact range

**Theorem 3.1 (primitive defect and ray flag).** For every $u\in\mathcal T$
and $k\in\mathbb N_0$,

$$
\begin{aligned}
d(u)&=c(p(u))\ge0,\\
d(\rho^k u)&=d(u),\\
e(u)=1&\iff d(u)=0.
\end{aligned}
\tag{IDC.3.1}
$$

The image of $d$ on all of $\mathcal T$ is exactly

$$
\{0\}\cup\{2,3,4,\ldots\}.
\tag{IDC.3.2}
$$

**Proof.** Apply (IDC.2.8) to the existing unique decomposition (IDC.2.2):
$c(u)=c(p(u))+\nu(u)$. Subtracting proves the first equality and
nonnegativity. Equations (IDC.2.3) and (IDC.2.8) increase both terms of
the difference by $k$, proving invariance.

The recurrence for $c$ gives $c(t)=0$ exactly for the leaf $\alpha$,
and $c(t)=1$ exactly for the leaf $\beta$: every pair has coordinate
at least two. Hence $c(p(u))=0$ exactly when $p(u)=\alpha$, proving the
flag equivalence. A primitive tree cannot have coordinate one because
the only such tree is $\beta=\rho\alpha\in I_1$.

For attainment of every remaining value, define finite trees

$$
p_0=\alpha,\qquad p_1=\beta,\qquad
p_m=(\alpha,p_{m-2})\quad(m\ge2).
\tag{IDC.3.3}
$$

This is a mathematical witness family, not an installed source construction
service. Induction gives $c(p_m)=m$. For $m\ge2$, its root pair cannot
be the special image $(\beta,\alpha)$ since its left child is $\alpha$,
and cannot be an ordinary image pair because that same child is outside
$I_1$. Thus $p_m\in\mathcal P$, $\nu(p_m)=0$ and $d(p_m)=m$.
The primitive $p_0=\alpha$ attains zero; $p_1$ is intentionally not a
primitive witness. This proves both inclusion and attainment in (IDC.3.2).
$\square$

**Example 3.2 (unbounded nonconstant intrinsic depth).** For every $m\ge2$
and $a\ge0$, the actual tree $\rho^a p_m$ has

$$
p(\rho^a p_m)=p_m,\quad \nu(\rho^a p_m)=a,\quad
c(\rho^a p_m)=m+a,\quad d(\rho^a p_m)=m,\quad e(\rho^a p_m)=0.
\tag{IDC.3.4}
$$

On the separate atomic ray $T_a=\rho^a\alpha$, the corresponding values
are $\nu(T_a)=c(T_a)=a$, $d(T_a)=0$ and $e(T_a)=1$. The calibration
consumer therefore includes all primitive trees and unbounded intrinsic
depths, rather than only atomic trees or a fixed-word family.

## 4. Actual acquisition, complete retention and authentic later entry

**Assumption 4.1 (the entire preparation and later-use contract).** Fix
one common effective producer and one common effective consumer. Their
installed programs and source-independent constants are the same for
every source. The following interfaces and services are separately
supplied and priced.

1. Preparation presents an unknown $u\in\mathcal T$ through the original
   raw address interface, stationary during this traversal. Starting at
   the actual root, the producer reads each present node once, expanding
   the two children only after a branch reply. It restores $u$ from
   these actual replies, then computes the finite inverse parsing and
   any proposed calibration $\lambda(u)$ on that description.
2. A complete retention cut leaves an authentic label $\lambda(u)$.
   Every other accessible source-dependent preparation field factors
   through this label. These fields include old outputs, retained
   archives, references, installation variants, caches, control location,
   addresses, counters, workspace contents and lengths, timestamps and
   any accessible termination-time information. Equal labels therefore
   give identical accessible preparation information under the same
   public task input. Random initialization, if present, is independent
   of the source conditional on that input and label. A readable source
   identity or archive carrying a further distinction is additional
   retained information and belongs in the label.
3. A supplied authentic same-source, same-root, forward-only presentation
   later gives $y=\rho^k u$ for an arbitrary unknown $k\in\mathbb N_0$.
   Every $u$ and every such $k$ is in the task domain. The invocation
   supplies no $k$, event count, initial intrinsic depth, source size,
   clock value or extra source-correlated input. The authenticity service
   gives this contract, not an identity token that distinguishes source
   pairs with equal labels. The current version remains quiescent during
   the entire consumer call.
4. The consumer gets the retained label at a separately supplied new
   task entry. Its only new source observations are actual original
   four-reply reads. The calibration comparison class chooses only
   $R^j$ requests; local computation and output are paid. It has no
   $\mathsf{ApplyRho}$, pairing, reset, equality, stream, event or clock
   oracle. A completed earlier call does not create a free future
   invocation or free archive access. Physical reply durations are not an
   observation of this four-reply model; a source-dependent timing port
   would enlarge the comparison interface.

The full-tree acquisition is the existing service of [ACQ] and [SLH,
Proposition 53.2][SLH]. Authentication, forward presentation, isolation, retention
lifetime, invocation and payment are hypotheses about supplied capabilities.
Neither the syntax of a construction context nor a mathematical invariant
manufactures any of these capabilities or proves their physical realization.
The complete cut is essential to the comparison: a forgotten tree whose
old source-dependent runtime or archive can still be read has not passed it.

**Proposition 4.2 (a common acquired defect producer).** Under Assumption
4.1, the existing traversal followed by finite inverse parsing computes
$d(u)$ on every actual $u$, and terminates sourcewise. Its preparation raw
read count and submitted address length are exactly

$$
2\ell(u)-1,\qquad
A(u)=\sum_{q\in\mathsf{Addr}(u)}|q|.
\tag{IDC.4.1}
$$

Parsing, local description construction, output and the complete cut are
additional costs. This is an upper construction, with no preparation,
work, retention or physical-cost optimality assertion.

**Proof.** Reuse [SLH, Proposition 53.2][SLH]'s traversal and reconstruction,
including its original finite node trace. Its actual node count is
$|\mathsf{Addr}(u)|$, and its literal length sum is $A(u)$. A full binary
tree with $\ell$ leaves has $\ell-1$ internal nodes, by the leaf base
case and addition across a pair; thus it has $2\ell-1$ nodes. After the
complete description is restored, Reuse 2.2's finite computation gives
$\nu(u)$ and the recurrence gives $c(u)$. Subtraction returns $d(u)$.
All these stages terminate on each finite source. Their workspace can
vary with the source; the cut does not retroactively remove their costs.
$\square$

## 5. The least retained distinction for right-spine continuation

**Definition 5.1 (exact calibration schemes and refinement).** A label
scheme is a map $\lambda:\mathcal T\to\Lambda$ effectively computed by
an allowed prepared producer, with the complete cut of Assumption 4.1.
It admits exact right-spine continuation if one common effective
consumer, using only that label, common public inputs, paid local
computation and raw $R^j$ replies, terminates and returns
$\nu(\rho^k u)$ for every $u\in\mathcal T$, $k\ge0$.
There is no uniform read or workspace bound in this definition.

A label $\lambda$ refines $d$ when
$\lambda(u)=\lambda(v)\Rightarrow d(u)=d(v)$. This compares persistent
preparation distinctions, not complete controller states or encoding
lengths. It allows $\lambda$ to depend on any part of the full acquired
$u$. A semantic factor on an arbitrary encoded label is not automatically
an effective decoder.

**Theorem 5.2 (necessary retained calibration and attainable least
partition).** Every exact right-spine continuation scheme satisfies

$$
\forall u,v\in\mathcal T,\qquad
\lambda(u)=\lambda(v)\ \Longrightarrow\ d(u)=d(v).
\tag{IDC.5.1}
$$

Conversely, the acquired scheme $\lambda(u)=d(u)$ admits an exact
consumer. Its persistent preparation partition is therefore the least
possible distinction for this task: it is attained, and every other
sufficient scheme refines it. The same necessity holds for randomized
consumers that terminate with the exact answer with probability one on
every promised input.

**Proof of necessity.** Suppose two actual prepared trees $u,v$ have
$\lambda(u)=\lambda(v)$ and $d(u)\ne d(v)$. Take a natural number

$$
C\ge\max\{c(u),c(v)\},\qquad
k_u=C-c(u),\qquad k_v=C-c(v).
\tag{IDC.5.2}
$$

Both lags are nonnegative and are therefore legal, separately for these
two actual presentations. Put $y_u=\rho^{k_u}u$ and $y_v=\rho^{k_v}v$.
The supplied coordinate advancement gives

$$
c(y_u)=c(y_v)=C.
\tag{IDC.5.3}
$$

Formula (IDC.2.9) then gives equal replies at **every** $R^j$, including
arbitrarily long, absent and repeated requests. The complete cut and
common public input give equal accessible initial consumer states.
Induct over the deterministic execution: equal current states give the
same local computation, next address, output or halt choice; at the
same permitted address the equal replies give equal successor states.
Thus the complete chronological traces and answers agree, however
many reads or how much computation are used.

Nevertheless (IDC.2.3) gives

$$
\begin{aligned}
\nu(y_u)&=\nu(u)+C-c(u)=C-d(u),\\
\nu(y_v)&=\nu(v)+C-c(v)=C-d(v).
\end{aligned}
\tag{IDC.5.4}
$$

These answers differ. Exactness on both actual inputs is impossible.
The aligned lags are chosen only to construct two admissible inputs;
the observer receives neither lag and performs no update.

For a randomized consumer, couple its source-independent random choices
identically on the two inputs. Every permitted conditional state and reply
law remains identical, so the output laws are identical. One law cannot
put probability one on each of the distinct answers in (IDC.5.4).
Probability-one termination adds no distinction and does not avoid the
contradiction.

Sufficiency is the acquired producer of Proposition 4.2 together with
Theorem 6.2's consumer. The resulting label is exactly $d$, so its
partition is achieved. Necessity says that the map sending an attained
label $\lambda(u)$ to $d(u)$ is well-defined; it supplies the claimed
refinement. An arbitrary alternative label still needs an effective
means of decoding this map to obtain an algorithm. $\square$

**Example 5.3 (actual indistinguishable current right spines).** Take
$u=\alpha$ and $v=(\alpha,\beta)=p_3$. They have $d(u)=0$, $d(v)=3$.
At lags $3$ and $0$, the current trees are respectively

$$
y_u=((\beta,\alpha),\beta)=T_3,qquad y_v=(\alpha,\beta).
$$

Both have coordinate three. Their complete right-spine maps are
$\mathsf{br}$ at the root, $\beta$ at $R$, and $\mathsf{abs}$ at every
$R^j$, $j\ge2$. Their intrinsic depths are three and zero. The original
left address $L$ distinguishes these current trees, which directly
shows why the right-spine restriction in the theorem matters.

**Theorem 5.4 (sharp persistent calibration alphabet).** For a known
$D\in\mathbb N_0$, restrict preparation to

$$
U_D=\{u\in\mathcal T:d(u)\le D\},
$$

and still allow every unknown $k\ge0$. Under the same complete cut and
right-spine competitor contract, the minimum cardinality of an attained
calibration alphabet is

$$
M(D)=
\begin{cases}
1,&D=0\text{ or }D=1,\\
D,&D\ge2.
\end{cases}
\tag{IDC.5.5}
$$

Without a defect bound, no finite calibration alphabet suffices.
With known $D$, a minimal fixed-length binary calibration payload has
$\lceil\log_2 M(D)\rceil$ bits, before framing, authentication and
retention costs.

**Proof.** Theorem 3.1 and its concrete witnesses give

$$
d[U_D]=
\begin{cases}
\{0\},&D\le1,\\
\{0,2,\ldots,D\},&D\ge2.
\end{cases}
$$

The necessity proof of Theorem 5.2 restricts without change to any pair
in $U_D$: both lags in (IDC.5.2) remain allowed and defect invariance
keeps both presentations in the same defect-bounded domain. Thus a
sufficient label must distinguish all these defect values. Their number
is (IDC.5.5). Retaining $d$ attains this bound.

For $D\ge2$, encode $d=0$ by rank zero and $d=m\ge2$ by rank $m-1$;
these are exactly the $D$ ranks $0,\ldots,D-1$. A binary field of width
$\lceil\log_2D\rceil$ holds them all, and $b$ fixed-length bits cannot
hold more than $2^b$ values. For $D=0,1$, the single calibration value
requires zero payload bits; this does not erase its invocation or
physical-service costs. Since the actual witnesses $p_m$ realize
arbitrarily many distinct defect values, the same necessary refinement
excludes every finite alphabet on the unbounded domain. $\square$

## 6. An effective later consumer with literal resource bounds

**Definition 6.1 (raw right-spine search).** A current invocation starts
with its authentic retained $d=d(u)$ and no knowledge of
$K=c(y)$. The following common program searches the stationary current
$y$.

First read $R^0=\varepsilon$. If it is $\alpha$ or $\beta$, set
$K=0$ or $K=1$, respectively. Otherwise its promised authentic reply
is $\mathsf{br}$. Read $R^1,R^2,R^4,R^8,\ldots$ in that order until
the first nonbranch reply. A leaf reply at $R^j$ immediately gives
$K=2j$ or $K=2j+1$ and ends the search.

If the first nonbranch reply is absent at $R^b$, let $a$ be the previous
branch index, using the already read root if $b=1$. Search strictly
between $a$ and $b$: read $R^j$ at
$j=\lfloor(a+b)/2\rfloor$. A leaf reply ends the search with its
corresponding $K$. A branch replaces $a$ by $j$; an absent reply replaces
$b$ by $j$; repeat. All submitted requests are literal words. Once $K$
is acquired, compute and output

$$
\widehat\nu=K-d,\qquad
\widehat Q=(K-d,\mathbf1_{\{d=0\}}).
\tag{IDC.6.1}
$$

A violated promise is outside the exactness domain; the algorithm's
correctness does not certify the retention or source contract.

**Theorem 6.2 (all-source calibrated readout).** Under Assumption 4.1,
with $d(u)$ prepared and retained, for every actual $u\in\mathcal T$
and every unknown $k\ge0$, Definition 6.1 terminates on $y=\rho^k u$
and returns exactly

$$
\widehat\nu=\nu(y)=c(y)-d(u),\qquad
\widehat Q=Q(y)=(\nu(y),\mathbf1_{\{d(u)=0\}}).
\tag{IDC.6.2}
$$

Let $K=c(y)$ and $L_K=\lceil\log_2(K+2)\rceil$. Its actual raw read
count $q$, maximum submitted address length and total submitted length
satisfy

$$
q\le2L_K+3,\qquad
\max_{\text{actual reads}}|R^j|\le K+2,\qquad
\sum_{\text{actual reads}}|R^j|\le(K+2)(2L_K+3).
\tag{IDC.6.3}
$$

It performs no source update. These are upper bounds for this consumer,
not a minimum-query theorem or a total-computation bound.

**Proof.** Put $h=\lfloor K/2\rfloor$ and $b_*=K-2h\in\{0,1\}$.
The existing raw formula (IDC.2.9) says that the right-spine replies
are branch precisely for $j<h$, the leaf of bit $b_*$ at $j=h$,
and absent precisely for $j>h$. Thus the initial leaf case obtains $K$
exactly and uses one raw call.

In the branch case $h\ge1$. Let $t$ be the least nonnegative integer
such that $2^t\ge h$; it exists for this finite $h$. Exponential search
has exactly the $t+1$ indices $1,2,\ldots,2^t$ before its first
nonbranch reply. If $2^t=h$, that reply is the required leaf. Otherwise
$2^t>h$, $t\ge1$, and the preceding branch at $a=2^{t-1}$ and the
absent upper index $b=2^t$ give

$$
a<h<b.
\tag{IDC.6.4}
$$

Every nonleaf midpoint update preserves this strict bracket. Its width
becomes at most the ceiling of half the preceding width. Starting from
$2^{t-1}$, after at most $t-1$ nonleaf updates the width would be at
most one, which is impossible for a bracket containing the integer
$h$ strictly. Consequently a leaf is reached in at most $t$ midpoint
reads. Equivalently, a width-two bracket has its unique integer midpoint
at $h$ and must give a leaf. No unqueried leaf label is inferred for
free. Every actual search is therefore finite and obtains $K=2h+b_*$.

Since $h\ge1$ and $t=\lceil\log_2 h\rceil$, $t\le L_K$.
The root, exponential probes and at most $t$ midpoint probes give
$q\le1+(t+1)+t=2t+2\le2L_K+3$. The immediate-leaf branches satisfy
the same bound. Minimality of $t$ gives $2^t\le2h$ (also for $t=0$).
Every midpoint index is at most this exponential endpoint, so every
submitted word has length at most $2h\le K$, in particular at most
$K+2$. The root cases satisfy the stated bound too. Multiplying the
number of calls by the maximum literal length proves the total-length
upper bound, counting each actual request in its chronological place.

Finally Theorem 3.1 gives $d(y)=d(u)$ and
$c(y)-d(y)=\nu(y)\ge0$, while its flag equivalence gives
$e(y)=\mathbf1_{\{d(u)=0\}}$. These prove both outputs. The program
never needs $K$ as an input; $K$ only indexes the analysis of its actual
finite run. $\square$

**Corollary 6.3 (conditional mutual recovery of two boundary coordinates).**
On every actual continuation, with the authentic prepared $d$ retained,
the acquired right-spine coordinate and intrinsic depth recover each other:

$$
(d,K)\longmapsto(d,K-d),\qquad
(d,n)\longmapsto(d,n+d),\quad n=\nu(y).
\tag{IDC.6.5}
$$

They are inverses on their actual image. Moreover $(d,n)$ determines the
entire current right-spine reply map through (IDC.2.9) with $K=n+d$.
It does not recover the raw read events that acquired those replies.

**Proof.** Theorem 6.2 establishes $K=n+d$ on the promised image, so
the two arithmetic maps are inverse there. Substitution into the already
supplied four-reply formula determines each reply value. Neither map
constructs a request event, timestamp or receipt. $\square$

The persistent calibration is constant along the authentic forward ray,
while the later decoded depth is nonconstant and unbounded. The same
retained $d$ can serve any finite sequence of separately supplied quiescent
invocations on that ray, by applying Theorem 6.2 in each call. Newly retained
transcripts and fields are paid additional state; a fresh complete cut must
isolate them if the next call is again claimed to start with only $d$.
This is continued use of one actually acquired relational boundary, not
an event counter or an entitlement to a next invocation.

**Resource boundary 6.4 (indices, literal words and complete storage).**
The search can materialize one current address buffer and overwrite it
between reads. With binary integer representations, its indices, bracket
endpoints, $d\le K$, parity and output integers need $O(\log(K+2))$ bits; the literal $R^j$ buffer needs
$O(K)$ workspace. Thus the logarithmic read bound does not give logarithmic
complete working memory or erase the submitted-word costs. If an actual
implementation retains a growing raw archive or multiple buffers, it must
add their storage. Preparation's tree description, traversal stack and
inverse parser have their own sourcewise storage and work.

For unbounded defects, the label is a finitely encoded natural for each
source, with no uniform finite alphabet. Known-$D$ payload widths in
Theorem 5.4 count only persistent calibration distinctions. They do not
count a program counter, installed decoder, framing, address workspace,
output, authentication material, protected storage or any other complete
controller field. No optimum for those fields, acquisition work, isolation,
energy or physical time is asserted.

## 7. Concrete limits and comparison domains

**Example 7.1 (actual entry and elapsed lag remain erased).** Preparation
at $u=\alpha$ followed by lag $k=1$, and preparation at $v=\beta$
followed by lag zero, both give current $y=\beta$ and retained $d=0$.
Their current intrinsic depth is correctly decoded as one. Their actual
entries and lags differ. Even the complete current tree and its entire
raw interface agree. This is the existing true-entry obstruction of
[JM, §37][JM] restricted to this calibration scheme; it supplies no new
entry-recovery result. Adding a retained $\nu(u)$ would permit
$k=\nu(y)-\nu(u)$, but would be additional retained preparation
information outside the least-$d$ scheme.

**Example 7.2 (all original-address readers have a different minimum).**
A consumer allowed arbitrary original addresses can start a paid native
traversal of the current stationary $y$, restore it, and apply the
existing finite inverse parsing to compute $\nu(y)$ with a constant
preparation label. It terminates sourcewise on every finite $y$.
Thus the absence of a finite calibration alphabet in Theorem 5.4 is
false for this larger observation class. The all-source full-tree
acquisition theorem and this right-spine calibration theorem have
different evidence and competitor domains.

**Example 7.3 (a sufficient depth boundary does not contain the brackets).**
The two primitive trees

$$
a=(\alpha,(\alpha,\alpha)),\qquad
b=((\alpha,\alpha),(\alpha,\alpha))
$$

both have $d=c=4$, $\nu=0$ and $e=0$. Their complete right-spine maps
agree, and after any common lag their $d$, $\nu$ and right-spine maps
still agree. They have different leaf counts and different left
subtrees. Hence the calibrated boundary does not reconstruct arbitrary
spatial interfaces, even after unlimited reads in its own subinterface.

**Example 7.4 (retained defect is not a pairing congruence).** Both
$\alpha$ and $\beta$ have $d=0$. Pairing them on the right with the
same $\alpha$ gives

$$
d((\alpha,\alpha))=2,\qquad
 d((\beta,\alpha))=d(T_2)=0.
$$

This is a direct limiting application of the supplied primitive parsing
and atomic ray, not a new context-quotient theorem. The calibration
partition is not stable under every spatial construction. After the
consumer has actually obtained $Q(y)$, [JM, (JM.135)–(JM.136)][JM] already
allows local calculation of depth under mathematical contexts with
other supplied operand $Q$ values. Such a calculation does not authorize
source pairing, create an operand observation or turn its predicted
result into a raw receipt.

**Contract boundary 7.5 (stationarity and authenticity cannot be omitted).**
The bisection invariant uses one fixed right-spine endpoint throughout
its raw calls. A changing version can invalidate that invariant; no
nonstationary-reader theorem is supplied. The output identity also needs
$d(y)=d(u)$. For example, transferring the prepared $d(\alpha)=0$
to an unrelated current $(\alpha,\alpha)$ gives the program output
$2$, while that current tree has intrinsic depth zero. This concrete
failure does not satisfy Assumption 4.1 and shows why same-source
forward-only presentation is a separate hypothesis. Neither a context
expression nor a matching scalar authenticates it.

Read chronology, query count, literal address length, internal computation,
retained memory, the actual number $k$ of substitutions after preparation,
the intrinsic inverse depth $\nu(y)$ and physical elapsed time are
separate quantities throughout. The program produces no actual substitution
and no physical-time estimate.

## 8. Source correspondence, attribution and the remaining bridge

All repository references below use the fixed mathematical snapshot
`782ca801d00c48d48e3b08553333b786bcf3e65e`. Source reading supplies statement
and parameter correspondence; it is not a fresh compilation or an axiom
closure audit.

| Supplier | Exact use and limit |
| --- | --- |
| [JM, §§36–37, 49–50, 65.1][JM] | Unique primitive rays, exact forward depth, finite image parsing, the flag $e$ and pair $Q$, the existing context composition, and erased-entry impossibility. These are reused, not re-established as new contributions. Fixed-word certificates in §§52–64 concern different observation fibers and are not granted as prepared inputs here. |
| [CLOCK], including private `clock_step` and `clock_at_step` | `rightClock`, exact advancement and four-reply right-spine intervals. The acquired service uses actual reads; later epoch-guarded original-address decoders from that module are not invoked because no epoch $k$ is supplied. |
| [ACQ], including the local suppliers of `source_foundation`, `acquisitionTrace`, `restore` and `acquisition_foundation`; [SLH, §§50, 53, 74–75][SLH] | Full native preparation, node/address costs and complete retention-cut discipline. Their complete old rows, relation fibers, authentic known epochs, original recut tasks and source-update menus are not the inputs or menu of the calibration consumer. |
| [ABC, §§1–2, 8][ABC] | All-source canonical atomic-block representation, advancing minimum rank and stationary structure. It already supplies a stronger mathematical representation than $Q$. It is not installed at the consumer's retained cut; its unrestricted acquired-relation decision obligation is not solved by this calibration. |
| [ARH, §6][ARH]; [TEMPLATE], including private `leaf_separation` and `right_tip_leaf`; [ANCESTOR] | Atomic-orbit right-spine consumers, known-template delayed certificates and full-word ancestor uniqueness. The first has an atomic-orbit promise, the second a known template and certified epoch, and the third full word and ancestor-coordinate inputs. None of those inputs is delivered here. Their exact results remain suppliers in their original domains. |
| [ALPHA, §§1–2][ALPHA]; [DIRECTION, §§1–3][DIRECTION] | Common finite stochastic generators, actual acquired alpha kernels and complete-law configuration risk for a stopped Fibonacci source. Their Read draws iid letters conditional on one random depth; repeating a native address here repeats a stationary literal-tree reply. Their risks, signed update statistics, priors and finite COMPLETE carriers do not supply the present defect-retention theorem. No probabilistic source correspondence is asserted. |

**Attribution 8.1 (ordinary deductions and mature background).** The new
source-specific continuation result is Theorem 5.2's lag-aligned obstruction
and the attained retained calibration, with Theorem 5.4's exact alphabet
and Theorem 6.2's charged raw consumer. Theorem 3.1 identifies the necessary
calibration from already supplied coordinates; Corollary 6.3 explains its
task-specific mutual recovery. These are `repo-derived` ordinary mathematical
deductions. Exact clock advancement, primitive-ray decomposition, complete
tree acquisition and $Q$ context composition keep their original ownership.
Elementary exponential bracketing, bisection and finite-label pigeonhole
arguments are not claimed as new general methods.

For the related mature context principle, Kozen's [author text][KOZEN],
*On the Myhill–Nerode Theorem for Trees*, states the tree-language theorem
for a finite ranked alphabet, ground terms, deterministic bottom-up tree
automata and all contexts with exactly one variable occurrence; its
statement and proof are on PDF pages 3–5. This is `literature-attested`
background for the context distinctions already used by [JM]. It does
not identify a retained preparation label with a bottom-up automaton state,
deliver an authentic later source, or prove our unknown-lag calibration
bound. No finite-state theorem is imported across that missing correspondence.

The bounded coverage comprises the owning sections and named public and
private source suppliers above. In this coverage the exact arbitrary-tree
retained-defect/right-spine-continuation result is not supplied. This is
neither a global repository-absence assertion nor an external originality
or priority claim. The evidence for the additions is their ordinary
proofs here; no Lean verification, numerical experiment or whole-project
admission conclusion is claimed.

**Open boundary 8.2 (the larger RRO task).** The attained boundary recovers
intrinsic depth and the existing $Q$ pair through an internally acquired
right-spine relation. It neither reconstructs arbitrary spatial boundaries
nor recovers true entry, event chronology or physical time. Pairing is
outside its operational domain. To extend this retained interface to an
actual spatial composition, one still needs separately acquired operands,
an authentic allowed construction service and a retained distinction
stable under that service, with its preparation, retention and later-read
costs. The $Q$ composition supplier alone does not deliver those capabilities;
Example 7.4 excludes using $d$ alone as their general composition state.
Unrestricted acquired morphic-fiber decisions, full interface recovery and
joint total-memory/work optima retain their original open obligations.
This finite continuation bridge does not complete the persistent RRO goal.

[JM]: https://github.com/the-omega-institute/trureturing/blob/782ca801d00c48d48e3b08553333b786bcf3e65e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md
[TM]: https://github.com/the-omega-institute/trureturing/blob/782ca801d00c48d48e3b08553333b786bcf3e65e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md
[SLH]: https://github.com/the-omega-institute/trureturing/blob/782ca801d00c48d48e3b08553333b786bcf3e65e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[ABC]: https://github.com/the-omega-institute/trureturing/blob/782ca801d00c48d48e3b08553333b786bcf3e65e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[ARH]: https://github.com/the-omega-institute/trureturing/blob/782ca801d00c48d48e3b08553333b786bcf3e65e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[CLOCK]: https://github.com/the-omega-institute/trureturing/blob/782ca801d00c48d48e3b08553333b786bcf3e65e/D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean
[ACQ]: https://github.com/the-omega-institute/trureturing/blob/782ca801d00c48d48e3b08553333b786bcf3e65e/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[TEMPLATE]: https://github.com/the-omega-institute/trureturing/blob/782ca801d00c48d48e3b08553333b786bcf3e65e/D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.lean
[ANCESTOR]: https://github.com/the-omega-institute/trureturing/blob/782ca801d00c48d48e3b08553333b786bcf3e65e/D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestorUniqueness.lean
[ALPHA]: https://github.com/the-omega-institute/trureturing/blob/782ca801d00c48d48e3b08553333b786bcf3e65e/docs/develop/theory/AURIC_FIB_ATOM_ACQUIRED_ALPHA_CALIBRATION_COMPATIBILITY.md
[DIRECTION]: https://github.com/the-omega-institute/trureturing/blob/782ca801d00c48d48e3b08553333b786bcf3e65e/docs/develop/theory/AURIC_FIB_ATOM_DIRECTIONAL_ALPHA_CALIBRATION.md
[KOZEN]: https://www.cs.cornell.edu/~kozen/Papers/mn.pdf

## 追加锚（本行以下为增补区）
