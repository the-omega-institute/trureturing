---
slug: peng-2026-zero-dimensional-shadowing-extension
bibkey: peng2026shadowing
doi: null
url: https://arxiv.org/abs/2606.14435v3
triage: wall
motivation_gids:
  - D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit.shadowing_inverse_limit_of_mittag_leffler
---

# Zero-dimensional shadowing extensions

## Problem

Peng's Question 5.1 asks whether every compact Hausdorff shadowing system
(X,f) is a continuous onto equivariant factor of a compact zero-dimensional
shadowing system (Y,g). Time is natural, including zero. Neither f nor g is
assumed invertible or onto; no metrizability or countable-weight condition
is imposed. Empty X has the solution Y empty. The general nonempty question
is unresolved here.

## Motivation

The reusable background bridge is preservation of finite-cover shadowing
by an arbitrary-directed compact Hausdorff Mittag-Leffler inverse limit.
It does not choose the symbolic stages or provide their bonding maps.

## Gap

A sufficient symbolic construction still requires all of the following:

1. Finite graphs at every finite observation scope, with edge-preserving
   deletion maps satisfying identities and every composition exactly.
2. Complete-path lifting for every target infinite path and every finite
   prefix, or genuinely proved ML stabilization of complete-path images.
   Vertex or edge surjectivity alone is insufficient.
3. Nonempty closed decoding cells, nested under every deletion, refining
   every finite open cover of X at some stage.
4. Actual graph-of-f witnesses for every stage edge, or a proved buffered
   closed-graph replacement implying sound limit decoding.
5. Complete coding of each actual orbit of each x in X at every stage.

Separate face lifts need not share one tracing orbit, and independently
constructed refinements need not commute around deletion squares. A
one-face refinement therefore does not settle the all-face construction.
A join-tree gluing theorem also requires its actual running-intersection
hypotheses and cannot be applied to cyclic proper-face scopes.

### Source feasibility criterion

For a once-fixed finite-face stage, suppose the vertical source relations
R_G are closed and symmetric. For a column v define its closed source cell
C(v) as the intersection of all constraints (v^G,x) in R_G. For a live finite
word w=v_0...v_m, meaning a prefix of an entire old stage path, define

$$
K(w)=\bigcap_{i=0}^{m}f^{-i}C(v_i).
$$

Every old whole array has one common constrained source orbit if and only
if K(w) is nonempty for every live finite word. The reverse implication
uses nested compact source sets for the same prescribed whole array. The
maximal source-array incidence is then compact and forward invariant; its
projection onto the entire stage is exactly this common-orbit condition.
These are ordinary mathematical reductions, not additional Lean theorems.

Arbitrarily fine proper-superface lifts of the same frozen old array force
this condition: shadow each lifted top row and take one compact subnet of
the source tracing points. Closedness preserves every old constraint in
the limit. For infinite coordinate indexing, monotone cofinal controls
provide the required proper-superface tail. Open relations give only their
closures under this argument, so closing a relation changes the target and
requires a separate construction choice.

The remaining existence obligation is to choose the controls and finite
alphabets globally, before any context or word is supplied, so that every
stage's live finite word has nonempty K(w). Source compactness does not
supply these finite feasibility facts. A failed word blocks every
sufficiently fine whole lift of arrays having that prefix, but does not
refute the existential question for other global choices.

A proposed finite visible/hidden graph can be checked against its entire
old path target using reachable hidden subsets. With N live visible and M
live hidden vertices, failure has a live prefix of length at most
N 2^M+1. This checks a fixed candidate; it does not prove a successful
candidate exists. Closed multivalued source itinerary images need not be
sofic even when the source has shadowing, so exact source-image pruning
cannot be assumed to terminate in a finite graph.

## Route

If this coherent family is constructed, compactness supplies its inverse
limit and the same-orbit coding fibers. Nested arbitrarily small cells give
unique decoding, edge soundness gives equivariance, the closed graph gives
continuity, and same-orbit fibers give surjectivity. The inverse-limit
shadowing theorem then supplies shadowing of Y. None of the missing
construction clauses is supplied by treating it as a hypothesis and calling
the original question solved.

## Falsifier

A coherent all-face construction would answer the question positively. A
scheme-specific lifting failure does not answer it negatively; a negative
answer requires a compact Hausdorff shadowing system admitting no such
extension by any construction.

## Evidence

The inspected primary source is Peng arXiv:2606.14435v3, Question 5.1 on
printed p.21. The independent source capsule also verifies the exact
Mittag-Leffler quantifiers of Definition 1.10. The self-contained inverse-limit
proof is in the cited Lean module; it does not assume that eventual-image
restrictions inherit shadowing.

## Triage

This is an unresolved construction question outside the metric case. The
Mittag-Leffler shadowing bridge is known-background infrastructure, not an
original question settlement.

### Projective-cover obstruction

The proposed construction "take a projective compact Hausdorff cover and lift
f" cannot supply a shadowing extension in general. This obstruction applies
to every projective cover of the following original shadowing source, not
only to one choice of lift. It does not refute Question 5.1.

Let X be the one-point compactification of discrete natural numbers, with
f(n)=n+1 and f(infinity)=infinity. Every finite open cover is refined by the
finite clopen partition

$$
\{\{0\},\ldots,\{K-1\},\{K,K+1,\ldots,\infty\}\}.
$$

Its quotient map commutes with the saturated successor map on
{0,...,K}. Use this same partition as the control cover. The partition labels
of any whole pseudo-orbit are an exact saturated-successor orbit. A sequence
beginning below K is traced by its finite initial point, and one beginning
in the tail is traced by infinity. Thus (X,f) has finite-cover shadowing.
Time zero is included, and f is not onto. X is already zero-dimensional, so
its identity map is a solution of Q5.1 for this source.

Suppose a compact extremally disconnected (Y,g) with continuous g and
shadowing admitted a continuous onto equivariant pi:Y->X. Set
U_n=pi^{-1}({n}). These are nonempty pairwise disjoint clopen sets and
g(U_n) is contained in U_{n+1}. Extremal disconnectedness makes

$$
W=\overline{\bigcup_{k\ge0}U_{2^k}}
$$

clopen. On U_n its indicator a is 1 exactly when n is a power of two:
for unselected n, the open U_n is disjoint from the selected union and
therefore from its closure. Let O be the union of all U_n. W is contained
in closure(O).

Consider any finite a-itinerary beginning with 1. Its finite-cylinder
preimage is a nonempty open set meeting closure(O), hence it meets some
U_n. Forward containment then realizes that same finite itinerary on
n,n+1,... in the discrete tube indices. In particular, if its first and
next 1 are at times 0 and d>0, then n and n+d are consecutive powers of
two. Thus d is itself a power of two. Conversely, every such distance
2^k occurs by starting on U_{2^k}.

The existing finite-observation theorem says that the entire a-itinerary
image of a shadowing system is the complete-path label language of one
finite graph. Suppose it has N vertices. Choose D=2^{N+2} and start an
actual orbit on U_D. Its initial word has 1 at times 0 and D, with 0 at
all times strictly between. Among graph vertices at times 1,...,N+1,
two agree; write their times as i<j. Erase the intervening zero cycle and
keep the original entire suffix. This remains an entire graph path and
has consecutive 1s at distance

$$
d=D-(j-i),\qquad 2^{N+1}<d<2^{N+2}.
$$

It must be an actual a-itinerary, while no power of two lies strictly
between these consecutive powers. This is a contradiction. Therefore
no extremally disconnected compact Hausdorff shadowing system admits
such a factor onto (X,f). Gleason's characterization identifies compact
Hausdorff projective spaces with extremally disconnected spaces, so the
same exclusion applies to all projective covers and all continuous
lifts of these dynamics.

The irreducible Gleason cover here is beta(N): the continuous extension
of N->X collapses the remainder to infinity. It is irreducible because
the singleton fibers over the dense isolated natural points force every
closed onto subset to contain their closure. Every continuous equivariant
lift agrees with successor on these singleton fibers, hence is the
unique continuous beta(N) successor extension by density. This particular
lift fails shadowing by the same argument.

Every continuous binary observation on X is eventually constant on the
natural points. Its clopen algebra is the finite/cofinite algebra.
Extremal disconnectedness completes the cover's clopen algebra far beyond
these source observations: the power-of-two tube coloring cannot descend
continuously to X. It is these extra cover observations that fail the
necessary finite-graph condition. Sofic observation languages alone are
only a necessary condition for shadowing; the obstruction does not replace
the remaining tracing and coherent-graph construction obligations by that
condition.

The general open-forward-tube obstruction is implemented in
`D5/S1/Dynamics/Shadowing/StoneanForwardTubeObstruction`.
The specialization to X, the shadowing proof for X, and the description
of its irreducible cover are mathematical exposition, not separate new
Lean declarations or an original open-problem settlement. The graph
construction, projectivity characterization and closure machinery are
reused; no worldwide novelty claim is made for their combination.

The remaining construction must use zero-dimensional covers with
controlled clopen observations, rather than projectivity alone. It still
must provide one globally chosen coherent finite-face family in which
every live finite word is source-feasible, with complete-path deletion
lifting or proved Mittag-Leffler stabilization. The projective obstruction
neither supplies this finite feasibility nor disproves existence of such
a family for arbitrary compact Hausdorff shadowing sources.

## ASSUMED-UNVERIFIED

No worldwide open-status conclusion is inferred from a bounded search. The
final Good–Meddaugh journal Theorem 8, pp.722-723, supplies the attributed
Mittag-Leffler preservation result, including nonsurjective bonds. Its Lean
formalization and subsequent freezing are separate from the still missing
coherent symbolic construction in this problem dossier.
