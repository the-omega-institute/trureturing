# Native finite obstructions for prescribed physical recovery budgets

This volume gives a terminating decision for each prescribed read and
update budget on the entire acquired signed fiber. Physical addresses
remain arbitrary finite words. A positive answer supplies a lawful finite
whole-fiber consumer; a negative answer supplies finitely many original
sources defeating every comparator within that budget, even when its
correctness requirement is relaxed to those sources alone.

The additional inference is a native finite-obstruction theorem, followed
by a two-sided effective search using native signed feasibility. Its
weighted application uses sums on each same source. Given a successful
finite consumer, it also supplies the missing logical input to the joint
resource frontier construction. Existence of some successful finite
budget, without such a witness, remains a separate obligation.

All proofs are ordinary mathematics. No Lean verification, implemented
decision procedure, complexity estimate or physical execution is asserted.

## 1. Entire original fibers and the precise comparison problems

**Assumption 1.1 (actual native input and complete handoff).** Use exactly
[ARH, Assumption 1.3][ARH], with

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,&
\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle x,y\rangle&=\langle\rho x,\rho y\rangle .
\end{aligned}
\tag{NFO.1}
$$

The sources are all nonempty finite ordered free trees, without a common
size, depth or shape promise. Put $\mathcal W=\{L,R\}^{*}$ and
$\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$.
The physical literal reply at an original-root address $p$ is $r_t(p)$.
For arbitrary finite prefix-free original cuts $P,Q$, a full old row
$R$, a finite literal history $H_0$, and a finite signed relation history
$H_{\rm rel}$, the nonempty admitted domain is exactly

$$
D=\mathcal U_R(H_0,H_{\rm rel})
 =\{u\in\mathcal T:R_P(u)=R,\ H_0(u),\ H_{\rm rel}(u)\}.
\tag{NFO.2}
$$

For a relation record $(i,s,j,t,\bowtie)$, both endpoints must exist and
$(\rho^iu)|_s\bowtie(\rho^ju)|_t$ compares entire reached trees.
Either sign is false if an endpoint is absent. Every record, old repeated
class, cross-class or off-task disequality, old existence guard and
concrete exterior is imposed on the same $u$.

The complete accessible entry has exactly this fiber. Every accessible
source-bearing cache, address, count, length, program counter, timing
field, reference, permission and archive belongs to the retained input.
The records were actually acquired before the cut. Their acquisition may
be finite sourcewise without a uniform bound. The same original-root
register is actually $\rho^Nu$, for supplied authentic $N$ at least every
acquired epoch. No new source identity or equality port is provided by
this authentication. The target throughout is the full original
$R_Q(u)$: reached original holes, complete concrete exterior and the
entire equality partition of the reached subtrees.

**Definition 1.2 (services and three different prices).** A comparator is
a common deterministic effective service, correct and terminating on
every source in its stated comparison domain, with actual operations
$\mathsf{Read}(p)$, forward same-register $\mathsf{ApplyRho}$, and
absorbing $\mathsf{Halt}$. Its common control may depend on actual replies.
There is no reset, reroot, clone, hidden selector, source-membership port
or uncharged source-related input. Updates expose no additional timing
channel. Define the sourcewise costs and worst-coordinate vector by

$$
\begin{aligned}
c_B(u)&=(q_B(u),a_B(u),\ell_B(u)),
&\ell_B(u)&=\sum_{\text{actual post-entry reads }p}|p|,\\
b(B)&=(\sup_Dq_B,\sup_Da_B,\sup_D\ell_B).
\end{aligned}
\tag{NFO.3}
$$

Here $q$ counts every actual raw read, including repeated calls and
absent replies; $a$ counts actual post-entry updates. A root read costs
one call and zero literal length. The length includes the whole physical
address, not just a class suffix. For rational $\lambda\ge0$, put

$$
W_\lambda(B)=\sup_{u\in D}
 [\lambda_q q_B(u)+\lambda_a a_B(u)+\lambda_\ell\ell_B(u)].
\tag{NFO.4}
$$

The sum precedes the supremum. Coordinate maxima can have different
realizing sources. Local computation, installation, address construction,
memory, output, authentication, retention and physical time are separate
resources; finite action counts do not assign prices to them.

**Definition 1.3 (prescribed budgets and relaxed finite obstructions).**
For integers $K,A\ge0$, let $\operatorname{Win}_D(K,A)$ mean that a
service meets $q_B(u)\le K$ and $a_B(u)\le A$ for every $u\in D$.
There is no literal-address-length bound in this predicate.

For a finite $S\subseteq D$, define $\operatorname{Win}_S(K,A)$ using
the same physical entry epoch, actions, common retained input and full
original target, but requiring correctness and budgets only on $S$.
The competing program may be designed using the complete finite list
$S$, hard-coded as common mathematical data. It still receives no actual
source index, membership answer or extra runtime observation. This is a
relaxation of the whole-domain comparison problem, not a new acquisition
claim for $S$. A finite obstruction is a finite $S\subseteq D$ for which
$\operatorname{Win}_S(K,A)$ is false.

For use with weighted path constraints, let
$\mathcal B\subseteq\{0,\ldots,K\}\times\{0,\ldots,A\}$ be a supplied
finite downward-closed set. Write $\operatorname{Win}_D(\mathcal B)$
when $(q_B(u),a_B(u))\in\mathcal B$ on every source. This includes a
rectangle and its intersection with
$\lambda_q q+\lambda_a a\le T$ for nonnegative weights. Downward closure
is essential when deleting uninformative actions.

**Convention 1.4 (falsifiers of the proposed interfaces).** The following
conditions delimit the claims before any decision result is used.
An original source omitted by (NFO.2), a spurious source admitted by it,
or an absent endpoint accepted under either sign falsifies source
fidelity. A shared terminal observation with different full original rows
falsifies behavioral sufficiency, including differences only in concrete
exterior or an off-task-induced partition bit. A backward update, hidden
source selector, unpaid equality query or simulated event reported as an
actual receipt falsifies physical legality. An excluded legal adaptive
comparator falsifies the optimality comparison. An increase on a same
source falsifies sourcewise dominance; replacing (NFO.4) by a sum of
separate maxima falsifies the weighted objective. An unbounded search
with no proof that one terminating branch must succeed falsifies a
decision claim. A negative sample that rejects only a chosen menu, while
permitting an untested physical word, falsifies obstruction completeness.
Finite examples cannot discharge these universal obligations.

## 2. Exact suppliers and finite observable control

**Convention 2.1 (native logical and paid suppliers).** The following
interfaces are reused with their exact premises.

| Supplier | Parameters here and permitted conclusion |
| --- | --- |
| [NSF Lemma 5.1 and Theorem 5.2][NSF] | The entire predicate (NFO.2), finitely many fixed epochs and words, and one or two original source variables. They decide joint feasibility, full-row equality or disagreement, with original witnesses. Words are not logical variables in these calls. |
| [NSF Theorem 7.2][NSF] | A fixed finite physical reply tree. It decides every path fiber and terminal full-row constancy, installs actual row outputs and computes exact sourcewise path costs and their maxima. |
| [NSF Theorems 7.3 and 8.1][NSF] | A supplied finite $(K,A,L)$ box. They decide it and its same-source weighted thresholds by finite skeleton enumeration. |
| [JRF Lemma 2.2, Theorem 3.1, Lemma 3.2][JRF]; [NSF Proposition 7.4][NSF] | Sourcewise late-epoch nonexpansive transport, an actual epoch cap and cached/constant-read cleanup on every finite native source. These require no literal-only source-language decision. |
| [ARH (2.3)][ARH]; [NSF Theorem 6.1][NSF] | Finite serial/static/prefix existence equivalence; effective checking and a paid static consumer for a supplied determining prefix. |
| [NPL Theorems 5.3, 7.1 and 8.2][NPL] | Entire row-image classification, exact source-fiber finiteness, and complete resources when the entire source domain really is finite. They do not supply a finite representative domain for an infinite fiber. |

JRF's literal-history $\mathsf{GB}$ and its matched WS2S source formulas
are not used on arbitrary signed histories. Its optimization construction
will instead receive the native decisions proved below.

**Definition 2.2 (physical skeleton and its exact leaves).** Use NSF
Definition 7.1. A finite four-reply tree has read vertices labelled by
fixed physical words $p_v$ and epochs $n_v\ge N$, nondecreasing along
paths, and absorbing halt leaves. Before each read it performs the actual
forward difference from the previous epoch. A halt performs no further
updates. Its full path fiber and path cost are

$$
\begin{aligned}
D_t&=\{u\in D:r_{\rho^{n_v}u}(p_v)=c(v,t)
                         \text{ for every }v\prec t\},\\
c_t&=(k_t,n_t-N,L_t),
&L_t&=\sum_{v\prec t}|p_v|,
\end{aligned}
\tag{NFO.5}
$$

where $n_t$ is the last read epoch, and a root halt has cost $(0,0,0)$.
Correctness means that each nonempty $D_t$ has a constant full $R_Q$.
Empty leaves impose no output or budget restriction. NSF gives exactly
these tests on entire signed path fibers and supplies a realizing source
for every nonempty leaf. No output-image finiteness premise is needed.

**Convention 2.3 (all-comparator unrolling and universal cleanup).** The
unrolling used in NSF Theorem 7.3 also applies when only $K,A$ are fixed.
After any reachable reply prefix, the next computation/update segment
and next read or halt are fixed by the common accessible state. A source
realizing that prefix certifies the segment is finite by source-totality.
At most $K$ replies give finitely many reachable prefixes. Unreachable
children become halts, and updates after the last read are deleted.
This yields a finite skeleton of depth at most $K$, with epochs in
$[N,N+A]$, preserving each source's reads and lengths and weakly reducing
its updates. There is no claim of extracting this unrolling by deciding
termination of arbitrary code.

The all-source normalization supplies, independently of $K,A$,

$$
M=\max(N,5),\qquad U=M-N,\qquad s_N=\max(0,2-N).
\tag{NFO.6}
$$

After capping, the same-source output is unchanged and
$q^c=q$, $a^c=\min(a,U)$, $\ell^c\le\ell$. Further cleanup only reduces
costs and gives

$$
q'(u)\le\ell'(u)+s_N .
\tag{NFO.7}
$$

The root can supply a new nonconstant reply only at epochs zero and one;
repeated same-epoch requests can use their acquired value locally.
Early decisions and genuine early halts remain legal. These are reused
sourcewise facts, not claims that the normalized receipt list equals the
original list. Deleted or simulated events create no actual receipts.

## 3. Native address limits and finite obstruction completeness

**Lemma 3.1 (finite-support limits of physical read trees).** Fix $K,A$.
Consider a sequence of finite physical skeletons of read depth at most
$K$ and epochs in $[N,N+A]$. There is a subsequence with a fixed tree
shape, fixed epoch at every read vertex, and, at each such vertex, either
a fixed physical word or a sequence of words leaving every finite subset
of $\mathcal W$.

Give an escaping vertex the auxiliary label $\infty$ and define its
auxiliary reply to be $\mathsf{absent}$. For each fixed original source
$u\in\mathcal T$, its complete reply path in the selected skeletons is
eventually the reply path in this finite auxiliary tree. The assertion
holds jointly for any fixed finite collection of original sources.

Proof. There are finitely many rooted four-reply shapes of bounded depth
and finitely many monotone epoch assignments. Select an infinite
subsequence on which these choices are fixed. There are now finitely
many word coordinates. For one coordinate, if some word occurs infinitely
often, restrict to those indices. Otherwise each word occurs finitely
often; since the word set is countable, select successively indices
outside each increasing finite initial word set. This coordinate then
leaves every finite set. Repeat for the finitely many coordinates.
Earlier properties persist under subsequences.

The native fact making this compactification useful is

$$
\{p:r_{\rho^n u}(p)\ne\mathsf{absent}\}
       =\operatorname{Pos}(\rho^n u),
\qquad |\operatorname{Pos}(\rho^n u)|<\infty .
\tag{NFO.8}
$$

It holds for every finite original $u$ and every fixed finite $n$ because
(NFO.1) maps finite trees to finite trees. Thus an escaping word coordinate
at epoch $n$ eventually has exactly the auxiliary absent reply on $u$.
A constant word coordinate has its fixed literal reply. There are only
finitely many vertices, so all their replies stabilize simultaneously
for this $u$. Induction down the fixed finite tree then stabilizes the
entire path, including early halts. Take the maximum of these finitely
many stabilization indices for finitely many chosen sources.

The subsequence step is the standard finite-product compactness argument
for the one-point compactification of a countable discrete set. Its
native input is (NFO.8), not a uniform depth bound for the whole fiber.
No procedure computing the stabilizing subsequence is asserted.
$\square$

**Theorem 3.2 (whole-domain prescribed-budget finite obstruction).** Under
Assumption 1.1, for every supplied finite downward-closed
$\mathcal B\subseteq\{0,\ldots,K\}\times\{0,\ldots,A\}$,

$$
\boxed{
\operatorname{Win}_D(\mathcal B)
\quad\Longleftrightarrow\quad
\forall S\subseteq D\text{ finite},\
                  \operatorname{Win}_S(\mathcal B).
}
\tag{NFO.9}
$$

When the left side holds it has a finite lawful physical skeleton witness.
When it fails there is a finite original-source obstruction. In particular
this holds for the rectangle defining $\operatorname{Win}_D(K,A)$, with
no bound on physical word length and no assumption that $R_Q(D)$ or $D$
is finite.

Proof. Restriction of a whole-domain service proves the forward direction.
For the converse suppose every finite subset admits a service. Exhaust
$D$ by the finite sets $S_j$ of admitted trees of size at most $j$; omit
initial empty sets. If $D$ is finite, repeat its eventual full set.
The sequence is increasing and every original source eventually belongs
to it. For each $j$ take a service correct only on $S_j$ and satisfying
$\mathcal B$ there. Convention 2.3, applied to that comparison domain,
unrolls it to a finite physical skeleton. Deleting terminal updates
preserves membership in $\mathcal B$ by downward closure.

Apply Lemma 3.1 to these skeletons. The selected indices remain unbounded,
so every fixed pair $u,v\in D$ belongs to all sufficiently late selected
$S_j$. Ignore the skeletons' terminal output labels during this selection:
these labels can range over an infinite set and are not being compactified.
Let $T$ be the resulting finite auxiliary tree.

If $u,v$ reach the same leaf of $T$, Lemma 3.1 says they reach that same
leaf of each sufficiently late selected skeleton. Both sources then
belong to that skeleton's correctness set $S_j$, so
$R_Q(u)=R_Q(v)$. This proves full-row constancy on every nonempty leaf of
$T$, without ever stabilizing an unbounded output label. For a fixed
$u$, its eventually stable path has the fixed read count $k_t$ and final
epoch $n_t$. Its late skeletons obey $\mathcal B$, hence
$(k_t,n_t-N)\in\mathcal B$ in the auxiliary tree as well.

It remains to turn this auxiliary object into an actual service.
At each $\infty$ vertex follow only its absent child and remove the
vertex. Do not send an infinite word to the source. Retained ordinary
read vertices keep their fixed finite words and absolute epochs. Between
two retained vertices execute just the forward epoch difference. If a
path now ends in a halt, omit updates after its last retained read.
All remaining epochs are monotone and at least $N$; the number of actual
updates is its last retained read epoch minus $N$. On each same original
source, induction through retained vertices gives exactly the same leaf
as in $T$. Removal decreases the read count and cannot increase updates.
Consequently its actual pair still lies in $\mathcal B$.

The finite tree now contains only lawful finite-word reads, actual
forward updates and halts. At each nonempty leaf install its common full
row. These finite outputs exist by the constancy already proved. On this
native signed domain their values can also be obtained effectively:
apply NSF Theorem 7.2 to the remaining tree's fixed path fibers. That test
returns a finite source witness for each nonempty fiber and hence its
actual row. Empty leaves can receive any fixed default row.

This is a deterministic effective finite program correct on the entire
original $D$. The auxiliary absent labels were used only to prove its
existence and never became source operations or receipts. The reverse
implication is established. Contraposition gives a finite obstruction
when no whole-domain service exists. $\square$

**Proposition 3.3 (why generic compactness alone is insufficient).** The
parameter space underlying Theorem 3.2 can be written as the finite
disjoint union, over shapes and epoch assignments, of
$(\mathcal W\cup\{\infty\})^V$, where $V$ is the finite read-vertex set.
For each original $u$, its auxiliary leaf and $(q,a)$ path pair are
continuous finite-valued functions on this space. For each pair $u,v$,
the condition that a common leaf implies $R_Q(u)=R_Q(v)$ is closed.
Budget conditions are closed as well. Finite collections of these
conditions involve finitely many original sources.

Proof. Equation (NFO.8) makes each reply function continuous at $\infty$
in the cofinite-neighborhood topology; continuity at ordinary words is
immediate because they are isolated. Finite tree evaluation is then
continuous by induction. Equality of finite-valued leaves and membership
in the supplied finite budget set are clopen. If the two fixed target
rows disagree, the pair condition is simply different leaves; otherwise
it is automatic. This proves the assertions.

The existing compact-realization suppliers therefore describe the
intersection principle in the middle of the proof. They do not establish
(NFO.8), eliminate auxiliary vertices into actual same-register actions,
handle full original rows by pairs, or give either effective search in
§4. Those are indispensable native hypotheses and constructions.
$\square$

## 4. Deciding the two sides without a physical-word bound

**Lemma 4.1 (exact negative-certificate verification).** Given a finite
list $S\subseteq D$ and a supplied $\mathcal B$ as in Theorem 3.2, one
can decide $\operatorname{Win}_S(\mathcal B)$ by a finite calculation,
covering every same-interface adaptive physical comparator, including
arbitrarily long words. Membership of each listed source in $D$ is also
decidable from the full original input.

Proof. Compute each finite $\rho^n u$ for $u\in S$ and
$N\le n\le N+A$, together with its literal reply table and full original
$R_Q(u)$. At epoch $n$ let

$$
\mathcal P_{S,n}=\bigcup_{u\in S}\operatorname{Pos}(\rho^n u).
\tag{NFO.10}
$$

This is a finite effectively listed set, and every word outside it
returns absent on every source in $S$. Enumerate depth-at-most-$K$
skeletons with monotone epochs in $[N,N+A]$ and words in
$\mathcal P_{S,n}$ at epoch $n$. Use the table to determine each leaf's
exact subset of $S$. Accept just when every nonempty subset has a
constant full row and its path pair lies in $\mathcal B$.
A passing skeleton physically realizes that table with the installed
row at every reachable halt, so it is a lawful comparator on $S$.

For completeness take any allowed comparator on $S$, unroll it as in
Convention 2.3, and at any vertex whose reply is constant on its current
candidate subset supply that reply locally and remove the read. In
particular every read outside (NFO.10) is removed. Keep the absolute
epochs of surviving reads; combine intervening updates into their actual
forward differences and omit final unused updates. On every same source
the output is unchanged and each cost weakly decreases. Every remaining
read lies in (NFO.10), every nonempty halt subset has a constant full row,
and downward closure preserves $\mathcal B$. Thus one enumerated tree
passes. This proves all-comparator completeness of a failing table test.

This is exactly the finite-support menu principle in NPL Lemma 7.2 and
Theorem 8.1, applied to the explicitly relaxed comparison set $S$.
It does not assert that $S=D$ or that sample membership is a runtime port.
The physical calculations on candidate trees are offline mathematics;
only the service's actual reads select its branch on its unknown source.
Checking $u\in D$ computes its entire old row, every finite recorded
iterate, both endpoint guards and every signed whole-tree comparison.
No constraint is discarded. The empty sample is feasible vacuously and
is never a negative certificate. $\square$

**Theorem 4.2 (terminating native arbitrary-word budget decision).** Given
Assumption 1.1 and finite $K,A$ or a supplied finite downward-closed
$\mathcal B$ within their rectangle, there is a terminating procedure
returning exactly one of:

1. a finite lawful whole-$D$ controller meeting the prescribed condition;
2. a finite nonempty $S\subseteq D$ whose exact table test in Lemma 4.1
   rejects every comparator on $S$ under that condition.

There is no supplied bound on physical words and no finite-source,
finite-image or determining-prefix premise.

Proof. Run two effective enumerations in interleaved finite stages.
For the positive enumeration, enumerate finite skeletons of read depth
at most $K$, monotone epochs in $[N,N+A]$, and all tuples of finite words.
For example at stage $j$ enumerate all such skeletons whose words have
length at most $j$. Every stage is finite and every candidate is eventually
included. Apply NSF Theorem 7.2 to every candidate on the entire $D$.
Check full-row constancy and the prescribed path pair at each nonempty
leaf. On success, use its actual original witnesses to install the full
outputs and return that finite controller.

For the negative enumeration, at stage $j$ list all finite native trees
of size at most $j$, retain exactly those satisfying (NFO.2), and perform
Lemma 4.1 on the resulting $S_j$. If it rejects, return $S_j$, its full
rows and its finite physical reply tables. Each stage finishes even if
$D$ is finite: it enumerates ambient size shells, not a search waiting
for a nonexistent next admitted source.

Every inner operation terminates. A positive return is correct on the
entire $D$ by NSF; a negative return is correct against every comparator
on $S_j$ by Lemma 4.1 and therefore against every whole-domain comparator.
The two returns cannot both be valid. If a whole-domain service exists,
Convention 2.3 gives a finite skeleton with finitely many finite words,
so the positive enumeration eventually finds one. Otherwise Theorem 3.2
gives a finite obstruction $S$. Some $S_j$ contains it. A service on
$S_j$ would restrict to a service on $S$, so $S_j$ is also an obstruction
and the negative enumeration eventually returns. These exhaustive cases
prove termination without extracting the subsequence in Lemma 3.1.
$\square$

**Corollary 4.3 (read budgets with updates left unrestricted).** For every
supplied $K$, existence of a whole-domain service with $\sup_Dq\le K$
is decidable, with the same positive controller and finite negative
certificate alternatives. A negative certificate rejects even comparators
with no prescribed update or word-length bound.

Proof. Apply the sourcewise cap in Convention 2.3. A service with read
bound $K$ becomes one with the same read bound and update bound $U$.
Conversely a $(K,U)$ service is an unrestricted-update competitor.
Invoke Theorem 4.2 at $(K,U)$. On a finite rejecting sample the same cap
applies sourcewise to every comparator correct only there. Thus no
uncapped comparator on that sample can meet $K$ either. $\square$

**Proposition 4.4 (infinite output image as an existing early rejection).**
If NPL Theorem 5.3 returns an infinite full-row image, then for any fixed
$K$ its witness family provides a finite obstruction of $4^K+1$ sources,
independent of a supplied update bound.

Proof. Choose that many witnesses with distinct rows. A four-reply
controller with at most $K$ reads unrolls to a tree with at most $4^K$
leaves. At least two different rows must share a leaf. Deterministic
common control cannot output both there. This is NPL's finite-output
necessity, used as an early certificate rather than a new limitedness
criterion. Theorem 4.2 is needed also when the output image is finite.
$\square$

## 5. Same-source weighted thresholds, including zero weights

**Theorem 5.1 (weighted thresholds with prescribed read and update caps).**
For finite $K,A$, rational $T$, and $\lambda\in\mathbb Q_{\ge0}^3$, it
is decidable whether a whole-domain service satisfies simultaneously

$$
\forall u\in D,\quad
q_B(u)\le K,\quad a_B(u)\le A,\quad
\lambda\cdot c_B(u)\le T.
\tag{NFO.11}
$$

A true decision gives a finite lawful whole-domain controller. A false
decision gives a finite original $S\subseteq D$ rejecting every service
under the same caps and threshold, even when correctness is required
only on $S$. All zero-weight cases are included.

Proof. If $T<0$, nonnegative costs exclude success on any nonempty domain;
one native witness from NSF is already a rejecting sample. Let $T\ge0$.
If $\lambda_\ell=0$, use Theorem 4.2 with

$$
\mathcal B=\{(k,d):0\le k\le K,\ 0\le d\le A,\
                           \lambda_qk+\lambda_ad\le T\}.
\tag{NFO.12}
$$

It is finite and downward closed. Its per-leaf inequality is precisely
the same-source inequality (NFO.11), including when one or both remaining
weights vanish. It is not an inequality on separately maximized costs.

If $\lambda_\ell>0$, every successful sourcewise run has

$$
\ell_B(u)\le L=\lfloor T/\lambda_\ell\rfloor .
\tag{NFO.13}
$$

Use NSF's finite-box skeleton enumeration with $(K,A,L)$ and test
(NFO.11) on every nonempty leaf by NSF Theorem 7.2. Its all-comparator
unrolling only decreases actual costs, so every comparator satisfying
(NFO.11) has a passing candidate. Every passing candidate is itself a
lawful service with exactly its tested same-source path costs. This is
the positive decision and the existing finite-box supplier is sufficient.

For the asserted finite negative certificate, a failing candidate has
either a nonempty leaf violating the threshold, with an original-source
witness, or a leaf containing two original sources with different full
rows, with a two-source witness. There are finitely many candidate
skeletons in this box; gather these witnesses, choosing one failure for
each candidate. Their finite union lies in $D$. Every candidate still
fails on this union. Any service satisfying (NFO.11) on the union would
unroll into one candidate with words of length at most $L$, producing a
contradiction. The argument ignores output labels during enumeration;
a leaf with two different rows defeats every possible installed label.
Thus it covers all outputs, not a finite preselected output list.
$\square$

**Theorem 5.2 (inferred caps for an unrestricted weighted threshold).**
For $\lambda\ge0$ rational and rational $T$, it is decidable whether any
legal whole-domain service has $W_\lambda\le T$, with no prescribed
read, update or word-length cap. If $\lambda_q+\lambda_\ell>0$, a true
answer gives a finite physical controller; a false answer gives a finite
original-source sample rejecting every comparator at that threshold.
The same statement remains effective with an optional finite upper bound
on reads, on updates, or on both.

When $\lambda_q=\lambda_\ell=0$ and no read bound is imposed, the answer
is true exactly when $T\ge0$. Its supplied static source-total consumer
need not have a finite reply tree on an infinite domain. An optional
nonnegative update bound does not alter this conclusion.

Proof. Negative $T$ is excluded by any one source, as above. Suppose
$T\ge0$. For positive observation weight, apply the cap and cleanup of
Convention 2.3, preserving every same-source nonnegative weighted
inequality. All actual updates are then bounded by $U$. If an update cap
$A_0$ is supplied, use $A_* =\min(U,A_0)$; otherwise use $A_*=U$.
If $\lambda_a>0$, one may further intersect with
$\lfloor T/\lambda_a\rfloor$, although this is unnecessary for termination.

If $\lambda_q>0$, set

$$
K_* =\lfloor T/\lambda_q\rfloor .
\tag{NFO.14}
$$

If $\lambda_q=0$ and $\lambda_\ell>0$, set instead

$$
L_* =\lfloor T/\lambda_\ell\rfloor,\qquad K_*=L_*+s_N.
\tag{NFO.15}
$$

Equation (NFO.7) justifies this latter read cap without dividing by a
zero weight. Intersect $K_*$ with any supplied read cap. Any comparator
satisfying the requested threshold and optional caps has a normalized
competitor within $(K_*,A_*)$, with no increased same-source cost.
Theorem 5.1 therefore decides the original question. Conversely its
positive controller satisfies every original constraint. For a negative
sample, exactly the same normalization works on any comparator correct
only on that sample, so the sample excludes all original uncapped
competitors there as well. This supplies both comparison directions.

If both observation weights vanish and a finite read bound is imposed,
apply capping and Theorem 5.1 with that bound and $A_*$. This includes
all-zero weights with a prescribed finite read budget: that budget
remains a real recovery constraint.

Finally suppose both observation weights vanish and no read bound is
imposed. Reuse JRF Theorem 7.1's static whole-source traversal, whose
physical decoder is valid on every native finite source. At epoch $N$
decode the original root using actual paid reads, recurse into original
children only after a decoded branch, and stop at original leaves.
Every actual original tree is finite. The service recovers it, computes
$R_Q(u)$, and genuinely halts, with $a(u)=0$ on every source. This gives
weighted value zero and meets any nonnegative update cap. Its sourcewise
read and length costs are finite, but their suprema need not be finite.
No lower value is possible. The empty observation-weight case therefore
has the stated separate, effective answer. $\square$

**Proposition 5.3 (weighted certificates concern common realizations).**
For every finite skeleton tested in Theorems 5.1 and 5.2, weighted
feasibility is equivalent to checking $\lambda_qk_t+\lambda_a(n_t-N)+\lambda_\ell L_t\le T$ on
all nonempty whole-domain path fibers. Even when $b(B)$ is finite, this
is not equivalent in general to $\lambda\cdot b(B)\le T$.

Proof. Every actual source follows exactly one leaf and has precisely
(NFO.5) there. NSF supplies a source attaining each nonempty path cost,
so the maximum of the sums is the supremum (NFO.4). Separate coordinate
maxima can come from different leaves. JRF Example 8.3 already supplies
an entire admitted native fiber and a lawful service with sourcewise
vectors $(1,2,0)$ and $(2,0,1)$: weights $(1,1,1)$ give worst sum $3$,
whereas the sum of separate maxima is $5$. It is a literal-history fiber,
hence an allowed special case with empty additional signed history.
Its redundant updates precede halt and are actual paid actions.
$\square$

## 6. Conditional complete attained Pareto frontier

**Assumption 6.1 (a supplied successful finite witness).** In addition to
Assumption 1.1, supply either a finite physical skeleton correct on all
$D$, or a supplied $h$ for which

$$
\forall u,v\in D,\quad
[\forall |p|\le h,\ r_u(p)=r_v(p)]\Longrightarrow R_Q(u)=R_Q(v).
\tag{NFO.16}
$$

Both inputs can be checked by NSF. A YES witness from Theorem 4.2,
Corollary 4.3, or a positive-observation case of Theorem 5.2 also qualifies.
An arbitrary program with no finite witness or proved bound is not this
input. No algorithm extracting such a witness from arbitrary source-total
code is assumed.

**Definition 6.2 (the reused static upper witness).** A successful finite
skeleton yields a determining $h$: take the maximum length of its
physical read words, using $h=0$ for a root halt. Native original-prefix
locality states that an epoch-$n$ reply at $p$ depends only on original
replies through depth $|p|$. Induction through the finite tree therefore
makes equal original $h$-prefixes follow the same halt, hence have the
same full original row. This is the locality direction of ARH (2.3),
with the exact formal supplier `original_prefix_locality` in
[NativeDepthPatterns][D5-DEPTH].

For either input to Assumption 6.1, NSF Theorem 6.1 now supplies a finite
static consumer at the actual entry epoch, with computable upper bounds

$$
(K_0,0,L_0)=
\left(2(2^{h+1}-1),\ 0,\
2(2^{h+1}-1)(h+\lceil N/2\rceil)\right).
\tag{NFO.17}
$$

Its physical reads decode original literal values; they do not recreate
past receipts. The exact leaf costs may be smaller. Any sharper verified
static upper bounds may be used instead. A supplied serial witness with
positive update cost is not silently treated as a zero-update witness;
(NFO.17) is the actual static conversion.

**Theorem 6.3 (native replacement for the joint frontier's missing decision).**
Under Assumption 6.1, let

$$
\mathcal F_D=\{b\in\mathbb N^3:\exists B\ \forall u\in D,\ c_B(u)\le b\}.
\tag{NFO.18}
$$

The complete finite set $\operatorname{Min}(\mathcal F_D)$ is effectively
computable, nonempty and attained. For each of its vectors $v$ a finite
lawful whole-domain service has exact worst-coordinate vector $v$, and
original sources attaining each coordinate maximum can be supplied.
The upward closure of this returned set is exactly $\mathcal F_D$.
This comparison includes every adaptive physical competitor, not just
those using the supplied witness's addresses or output-discovery method.

Proof. Reuse JRF Lemma 5.2 and Theorem 5.3's optimization construction,
with the following explicit replacement of its logical suppliers.
The static upper witness is (NFO.17), the all-source normalization is
Convention 2.3, the unbounded-word $(k,d)$ decision is Theorem 4.2,
and the finite $(k,d,L)$ decision and exact costs are NSF Theorems
7.3 and 7.2. None of these requires literal-only $\mathsf{GB}$ or a
WS2S description of the signed fiber.

For completeness the finite cofinal rectangle and its stopping argument
are as follows. Put

$$
K_\circ=\max(K_0,L_0+s_N).
\tag{NFO.19}
$$

Given any correct comparator with finite worst vector, cap and clean it.
Write its worst read and length costs $q',L'$. It has updates at most $U$
and $q'\le L'+s_N$. If $q'\le K_\circ$, finite reply unrolling puts it
in that read/update rectangle without increasing its worst vector.
If $q'>K_\circ$, then $q'>K_0$ and
$L'\ge q'-s_N>L_0$. The static service (NFO.17) weakly dominates its
worst vector and also lies in the rectangle. This latter comparison is
between worst-coordinate vectors; it is not a sourcewise replacement
and is not used for weighted optimization.

For each of the finitely many pairs
$0\le k\le K_\circ$, $0\le d\le U$, invoke Theorem 4.2. Discard NO
pairs immediately. For each YES pair obtain its finite witness and
compute its exact finite worst length $L^{\rm wit}_{k,d}$ using NSF.
Search the finite interval $0\le L\le L^{\rm wit}_{k,d}$ by the native
finite-box decision to find its first feasible value $L_{k,d}$ and an
attaining-within-budget tree. Form

$$
\mathcal V=\{(k,d,L_{k,d}):0\le k\le K_\circ,\ 0\le d\le U,\ \operatorname{Win}_D(k,d)\},
\qquad \mathcal P_D=\operatorname{Min}(\mathcal V).
\tag{NFO.20}
$$

Every member of $\mathcal V$ is feasible. The cofinal rectangle argument
shows that every feasible finite vector dominates some member of
$\mathcal V$, hence a member of $\mathcal P_D$. This proves equality of
upward closures and then
$\mathcal P_D=\operatorname{Min}(\mathcal F_D)$.
A witness for a minimal vector cannot have any strictly smaller exact
worst coordinate while respecting the other coordinates: its own exact
worst vector would then be a smaller feasible vector. Thus the selected
witness attains the vector exactly. NSF's nonempty-leaf witnesses attain
its coordinate maxima, possibly on different original sources.

There are finitely many pair decisions; each terminates by Theorem 4.2.
Every YES has a finite witness, and only then is its bounded length
search started. This is the effective stopping argument. Dickson's
finiteness principle alone would not suffice. The supplied static service
makes the returned set nonempty. $\square$

## 7. Conditional rational minimax over all adaptive services

**Theorem 7.1 (all nonnegative rational weighted minima given success).**
Under Assumption 6.1, for every $\lambda\in\mathbb Q_{\ge0}^3$ the
unrestricted value

$$
W_\lambda^*=\inf_{B\text{ correct and total on }D}W_\lambda(B)
\tag{NFO.21}
$$

is a computable rational number, attained by a finite lawful physical
controller. An original source attaining that controller's worst weighted
sum can also be returned. Every zero-weight case is included.

Proof. This is JRF Theorem 7.1's same-source construction with the native
threshold decision of Theorem 5.2 in place of its literal-only logical
decision. The static witness gives

$$
T_0=\lambda_qK_0+\lambda_\ell L_0\in\mathbb Q_{\ge0}.
\tag{NFO.22}
$$

If both observation weights vanish, that finite static witness attains
zero, the smallest possible value. Otherwise choose a positive common
denominator $b$ of the three weights. Every sourcewise finite weighted
sum lies in $b^{-1}\mathbb N$. A nonempty bounded subset of this lattice
has a maximum in the same lattice. Hence any competitor with finite
$W_\lambda\le T_0$ has value on the finite list

$$
0,\ 1/b,\ 2/b,\ \ldots,\ T_0 .
\tag{NFO.23}
$$

Here $bT_0$ is an integer. Decide those thresholds in increasing order
by Theorem 5.2. The last is true because of the static witness, so a first
true threshold is found in finitely many terminating calls. Its positive
answer is a finite controller. A competitor of smaller value would either
have a smaller lattice value, contradicting the earlier NO decision, or
would violate the lattice fact. A competitor of value larger than $T_0$
or infinite cannot improve the returned value. These comparisons cover
all source-total adaptive services, including those with unbounded
zero-priced coordinates. NSF Theorem 7.2 supplies an original source
attaining the returned finite controller's weighted maximum.

In particular when $\lambda_\ell=0$ and $\lambda_q>0$, the decision at
each threshold uses the finite obstruction theorem with genuinely
unbounded physical words. When $\lambda_q=0$ and $\lambda_\ell>0$,
cleanup supplies the needed read cap from length. At no point is a
zero weight used as a divisor or a sourcewise objective replaced by a
sum of separate maxima. The Pareto set in Theorem 6.3 need not be the
right candidate family for (NFO.21); this proof does not optimize over
that set. $\square$

## 8. Sharp quantifier boundaries and native special cases

**Proposition 8.1 (no finite sample can refute every finite budget).**
For every finite nonempty $S\subseteq D$, some finite static physical
service at entry $N$ recovers the full original $R_Q$ on $S$. In
particular, even on a whole fiber with no uniformly bounded recovery,
no one finite sample is an obstruction to all read budgets.

Proof. Native $\rho^N$ is injective, as supplied by ABC's all-source
conjugacy and the native injectivity results. Distinct original trees in
$S$ therefore have distinct current finite trees. Their union of present
positions is finite and distinguishes them by literal replies. Use NPL
Lemma 7.2's exact finite-source procedure: whenever the surviving source
subset has more than one full target row, choose a physical word that
separates two of those sources and read it at epoch $N$. Each nonempty
reply subset is a strict subset. At most $|S|-1$ such reads suffice;
the finite menu also gives finite total literal length. Stop as soon as
the surviving full rows agree. There are zero updates and no source
identity port. The list $S$ is common program data, and only actual paid
replies narrow it. This proves the claim in the relaxed comparison class
of Definition 1.3. $\square$

**Proposition 8.2 (the finite-partition obstruction remains a full-goal boundary).**
On the whole admitted fiber of all pairs with the root old row and the
literal original-root reply branch, take $Q=\{L,R\}$. Its full row image
has exactly the equal-child and unequal-child partitions, while no
uniform finite-read whole-row service exists. Nevertheless every fixed
budget has a finite obstruction as in Theorem 4.2, and no finite subset
refutes all budgets.

Proof. Reuse NSF Proposition 11.4 and NPL Example 9.4. For every $h$,
large native orbit trees supply
$\langle T_m,T_m\rangle$ and $\langle T_m,T_{m+1}\rangle$ with the
same original prefix through $h$ and different full partitions.
ARH (2.3) excludes every uniform finite-read service on that entire
fiber. It is an allowed instance with empty extra signed history and
its concrete exterior is fixed; no target replacement is involved.
Theorem 4.2 gives a finite obstruction separately for each prescribed
$(K,A)$, or Corollary 4.3 for each $K$ without an update cap.
Proposition 8.1 proves the last assertion. Thus the quantifiers are

$$
\forall K\ \exists S_K\subseteq D\text{ finite}\
          \neg\operatorname{Win}_{S_K}(K,U),
\tag{NFO.24}
$$

not $\exists S\ \forall K\ \neg\operatorname{Win}_S(K,U)$.
This reuses the established native counterexample; it is not a new
undecidability result. $\square$

**Proposition 8.3 (constant, empty-cut and zero-budget cases).** The
following cases remain within the preceding decisions.

1. $K=0$ is feasible exactly when the full $R_Q$ is constant on $D$,
   independent of $A$. NSF decides constancy and returns its row, or
   two original sources with different rows.
2. $Q=\{\varepsilon\}$ always has its constant one-hole row and cost
   $(0,0,0)$. $Q=\varnothing$ demands the entire original source;
   NPL Theorem 7.1 already decides bounded recovery there by exact
   finiteness of $D$.
3. $A=0$ permits only static reads at the actual epoch $N$. No cap
   construction forces an early update. Absent words, born positions,
   repeated old classes and every retained off-task condition stay
   covered by the native path predicate.
4. The logical procedures can reject an inconsistent input as empty
   using NSF. An empty mathematical comparison set is vacuously feasible;
   it is not an actual entry and is outside the nonempty service promise.

Proof. Without a new read, common control and nonobservational updates
give no new source distinction, so a terminating output is constant.
A constant row is supplied by one native witness and a root halt.
The second assertion is the full original-row definition and the named
NPL theorem. The third follows from the epoch interval in the finite
skeleton and from NSF's exact guard handling. The fourth follows from
native feasibility and elementary empty-domain quantification.
$\square$

**Open problem 8.4 (unrestricted existence and its unresolved classifications).**
On arbitrary nonempty (NFO.2), retain the question

$$
\exists K\ \operatorname{Win}_D(K,U)
\quad\Longleftrightarrow\quad
\exists h\ \operatorname{PrefDet}(D,Q,h).
\tag{NFO.25}
$$

The equivalence uses the all-source cap and ARH (2.3); it is an existence
correspondence, not a decision procedure. Theorem 4.2 decides each fixed
$K$, so YES instances of (NFO.25) can be found by enumeration. It supplies
no stage at which successive NO answers prove that every later $K$ is
also NO. Proposition 8.1 rules out a finite-source certificate with that
stronger all-budget meaning.

For positive observation weights, (NFO.7) and ARH's correspondence show
that some finite weighted threshold is feasible exactly when (NFO.25)
holds. Hence the general decision whether the Pareto set is empty, or
whether the optimum for positive observation weights is infinite,
remains subject to the same unresolved obligation. Theorems 6.3 and 7.1
are conditional on a supplied success; they do not classify failure
unconditionally. Each fixed weighted threshold is decidable, including
zero weights, but searching larger thresholds does not decide an
infinite optimum. If both observation weights vanish, the unconditional
zero optimum is already covered by Theorem 5.2 and is no exception to
this stated positive-observation boundary.

NPL's infinite-image classification, exact finite-source classification,
and the established recognized-family CAR, SRF, CRF and GRS decisions
retain their own stronger conclusions at their original premises.
Finite row image by itself does not settle (NFO.25). No global native
undecidability, new uniform source bound, or finite all-budget obstruction
is claimed.

## 9. Supplier correspondence, literature and the substantive increment

**References 9.1 (formal interfaces and exact applicability).** Public and
private source interfaces at the [repository baseline][BASE] distinguish
the existing formal supply from this ordinary increment.

| Source | Exact supplied premise and retained limit |
| --- | --- |
| [CompactLocalRealization][D5-COMPACT], `compact_local_realization` | A compact parameter space and closed record fibers, with every finite subfamily realized, imply simultaneous realization. The physical space and its closed native constraints must first be supplied as in Proposition 3.3. |
| [CompactSignatureRealization][D5-SIGNATURE], `finite_compatibility_global_realization` | Continuous readouts to Hausdorff coordinate spaces on a compact state space. It is an intersection supplier, not a native physical-word or paid synthesis theorem. |
| [NativeDepthPatterns][D5-DEPTH], `original_prefix_locality`, `depthEquiv`, private `fill_decompose` and `decompose_fill` | Original-prefix locality and exact original frontier reconstruction; the locality hypothesis is agreement at all addresses of length at most the queried physical length. It supplies Definition 6.2's conversion. |
| [NativeCutFibers][D5-CUT], `rowFiberEquiv`, private `recover_fill` and `fill_injective` | Actual full old-row fibers with repeated classes and every cross-class disequality, not a relaxation to independent marginal sources. |
| [NativeHistoryCells][D5-HISTORY], `cell_feasibility_exact`, `historyCellEquiv`, private `syntax_iff_ground` and `feasible_history` | Literal-history feasibility and exact full class cells. The history sort is a list of epoch/address/reply records, not arbitrary signed whole-subtree comparisons. NSF supplies those comparisons here. |
| [NativeSymbolicRecutting][D5-RECUT], `symbolic_recut_exact`, private `termAt_fill` and `exterior_commute` | The original reached order, concrete exterior and full partition after filling. It does not replace the full target by root labels. |
| [Pinned mathlib FreeMagma][FREE] | Free constructors, decidable tree equality and the universal lift; the native source correspondence is $\alpha=\mathtt{of\ true}$, $\beta=\mathtt{of\ false}$, pairing $\mathtt{mul}$. |
| [Pinned mathlib compactness][COMPACT] and [one-point compactification][ONEPOINT] | `CompactSpace.iInter_nonempty`, compactness of `OnePoint X`, and cofinite convergence from a discrete space. They supply standard topology, with no native source or cost correspondence. |

The additional native physical inference is
the implication from finite-source solvability to whole-source physical
solvability using finite support at each actual epoch, output comparison
by pairs, and elimination of the only added address limit. The negative
certificate verifier preserves all arbitrary-word competitors; the
positive verifier preserves all original sources. Neither direction is
supplied by an abstract compact-realization statement alone.

**References 9.2 (primary literature and bounded scope).** The
finite-intersection and one-point compactification principles are
literature-attested standard topology, used as intermediate methods.
The proof in Lemma 3.1 states the elementary finite-product selection
argument explicitly, so no stronger compactness or computability theorem
is imported. The pinned formal suppliers in References 9.1 specify its
mathematical hypotheses independently of historical attribution.

Solar-Lezama, Tancau, Bodik, Saraswat and Seshia,
[*Combinatorial Sketching for Finite Programs*][SKETCH], §5.4, give the
counterexample-guided synthesis method for their finitely represented
program setting. Candidate search and counterexample refinement are
literature-attested methods. Their termination argument exhausts the
finite $2^m$ input space of the Boolean encoding; it does not give an
arbitrary-word stopping rule on the infinite domain (NFO.2). Theorem 4.2 gets that rule
from Theorem 3.2 and a separate finite-sample all-comparator decision;
no termination premise is borrowed merely from the name of the method.

Kuncak and Rinard, [*On the Theory of Structural Subtyping*][KR],
arXiv:cs/0408015v1, §6, Theorem 90 and Corollary 91, supply quantifier
elimination and sentence decision for their specified term-power
language with a decidable base structure. That primary language and its
sentence-decision result do not assert definability of the native normal
subdomain or the physical-address sort. [TPO][TPO] retains its exact
normal-domain obstruction. This volume uses NSF's native fixed-word
queries and a separate search over physical words; it does not insert
an unsupported predicate into a term-power language.

The comparison is bounded to these synthesis and term-power sources,
the cited compactness interfaces, and the adjacent native repository
results. It supports no literature-wide novelty, priority or general
undecidability claim. Theorems 3.2 and 4.2 and their paid correspondence
are classified as repo-derived; §§5–7 are repo-derived applications of
that new bridge together with the exact NSF/JRF suppliers. NPL's
projection, finite-source and exterior results, and the existing
serial/static/prefix existence bridge, are reused rather than asserted
as new results.

**Proposition 9.3 (minimal additional relation and the remaining bridge).**
For the fixed source/action contract, the prescribed-budget gap is closed
by the following chain of supplied and new implications:

$$
\begin{aligned}
&\text{native fixed-word feasibility and finite-source physical tables}\\
&\quad+\ \text{finite-source obstruction completeness at fixed }(K,A)\\
&\quad\Longrightarrow\ \text{terminating arbitrary-word budget decision}\\
&\quad\Longrightarrow\ \text{same-source threshold decisions}\\
&\quad\Longrightarrow\ \text{complete resource minima given finite success}.
\end{aligned}
\tag{NFO.26}
$$

It does not imply a terminating decision of (NFO.25).

Proof. NSF already provides the first logical supplier, and finite
source tables follow from actual finite iterates as in NPL. Reusing
only those suppliers leaves an unbounded positive word search without
a negative stopping rule. Theorem 3.2 adds exactly the finite original
obstruction needed for the negative search, yielding Theorem 4.2.
Theorems 5.1 and 5.2 combine it with sourcewise nonexpansive cap and
cleanup; Theorems 6.3 and 7.1 supply the resulting exact optimization
consumers after a known successful static upper witness. These establish
the chain with actual same-register operations and the original full row.

No change to the source representation, no finite representative promise
and no extra equality observation is required. The relations that encode
memory remain the acquired guarded constraints; the original boundary
and its concrete spatial exterior remain the target; the authenticated
epoch remains the forward physical action coordinate. Their resource
comparison is made on the same source throughout. The chain addresses
how much paid access suffices at a prescribed budget; it does not turn
finite semantic alternatives into a free observable selector. Equation
(NFO.24) explains why its finite obstructions cannot terminate the outer
existential search in (NFO.25). That additional uniform inference remains
open. $\square$

**Status 9.4 (mathematical evidence boundary).** The statements of this
volume have ordinary proofs conditional on the named ordinary suppliers
and the actual acquisition/handoff assumptions. Formal source inspection
identifies existing interfaces; it is not a new compilation of their
application. Structural document checks do not verify these proofs.
No solver, experiment, receipt-producing physical run, independently
verified realization or unconditional solution of the continuing
minimal-relations programme is asserted.

[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[NPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md
[JRF]: RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md
[TPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_TERM_POWER_OBSTRUCTION.md
[BASE]: https://github.com/the-omega-institute/trureturing/tree/973aed8e8ab6d0517f5cc8b0d4b04abbffe9dfb6
[D5-COMPACT]: https://github.com/the-omega-institute/trureturing/blob/973aed8e8ab6d0517f5cc8b0d4b04abbffe9dfb6/D5/S3/Observer/Completion/CompactLocalRealization.lean
[D5-SIGNATURE]: https://github.com/the-omega-institute/trureturing/blob/973aed8e8ab6d0517f5cc8b0d4b04abbffe9dfb6/D5/S3/Observer/Prediction/CompactSignatureRealization.lean
[D5-DEPTH]: https://github.com/the-omega-institute/trureturing/blob/973aed8e8ab6d0517f5cc8b0d4b04abbffe9dfb6/D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[D5-CUT]: https://github.com/the-omega-institute/trureturing/blob/973aed8e8ab6d0517f5cc8b0d4b04abbffe9dfb6/D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean
[D5-HISTORY]: https://github.com/the-omega-institute/trureturing/blob/973aed8e8ab6d0517f5cc8b0d4b04abbffe9dfb6/D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.lean
[D5-RECUT]: https://github.com/the-omega-institute/trureturing/blob/973aed8e8ab6d0517f5cc8b0d4b04abbffe9dfb6/D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.lean
[FREE]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Algebra/Free.lean
[COMPACT]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/Compactness/Compact.lean
[ONEPOINT]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/Compactification/OnePoint/Basic.lean
[SKETCH]: https://people.csail.mit.edu/asolar/papers/asplos06-final.pdf
[KR]: https://arxiv.org/pdf/cs/0408015v1

## 追加锚（本行以下为增补区）
