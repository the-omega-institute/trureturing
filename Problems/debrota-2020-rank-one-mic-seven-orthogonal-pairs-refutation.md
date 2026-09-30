---
slug: debrota-2020-rank-one-mic-seven-orthogonal-pairs-refutation
bibkey: debrota2020varieties
doi: 10.1142/S0219749920400055
url: https://arxiv.org/abs/1812.08762v5
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.result
---

# A rank-one qutrit MIC with nine orthogonal pairs

## Problem

J. B. DeBrota, C. A. Fuchs and B. C. Stacey, “The Varieties of Minimal
Tomographically Complete Measurements”, arXiv:1812.08762v5 (quant-ph),
Conjecture 1 on printed page 6 states:

> A rank-1 MIC in dimension 3 can have no more than 7 pairs of orthogonal elements.

A MIC is a POVM of exactly d² positive semidefinite effects summing to the
identity whose real span is the Hermitian operators. Orthogonality is
`tr(E_a E_b) = 0`; distinct unordered pairs are counted once. Issue #11474
preregisters the literal reading for d = 3 before Lean implementation.
The conjecture imposes no unbiasedness condition, although its preceding
seven-pair example is explicitly called unbiased.

## Motivation

The zero entries of a MIC Gram matrix constrain the geometry of minimal
quantum measurements. The frozen declaration
`D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.result` negates
the universally quantified seven-pair bound using a rank-one qutrit MIC.

## Gap

The literature check recorded in #11474 found no settlement in the searched
scope. The citing-work scan is reported by a codex-cli search seat; the
source-version and MathDB checks are reported by the Claude Code orchestrator in that issue.
These are attributed readings, not an exhaustive literature or priority claim.
The different orthocross inverse-Gram conjecture is settled by
`OrthocrossGramHalfInteger.result`; it does not imply this pair-count bound.

## Route

For indices 0 through 8 let

```
v = [(1,i,-1), (1,-1,1+i), (1-i,0,-1), (1,-1+i,1+i),
     (0,1,i), (-1-i,i,1), (1,1,1), (1,i,-1-i), (1,-i,0)]
k = [3,2,2,4,3,3,9,7,11]
E_a = (k_a/46) v_a v_a†.
```

Positive scaling of an outer product gives positive semidefiniteness and
rank at most one; a nonzero diagonal entry proves rank at least one.
Entrywise complex arithmetic proves `Σ E_a = I`. Write x for the nine real
Hermitian coordinates `(H00,H11,H22,Re H01,Im H01,Re H02,Im H02,Re H12,Im H12)`.
The Lean source provides an integer matrix J such that the real coefficients
`c_a = (Jx)_a/k_a` reconstruct every Hermitian H as `Σ c_a E_a`.
The nine pairs `(0,1),(0,8),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8)`
have zero trace product, giving at least nine distinct unordered pairs.

## Falsifier

A failed positivity, rank, identity-sum, real-spanning or trace-zero check
would invalidate this counterexample. Using only real parts of traces or
counting both orders of a pair would change the claim. The formal definition
uses full complex trace equality and increasing pairs `a < b`.

## Evidence

The canonical Lean module has public definitions `IsRankOneMIC`,
`orthogonalPairs`, `claim`, and the sole theorem `result : ¬ claim`.
Its proof constructs all five MIC conjuncts, the nine-pair subset, its
cardinality nine, and the contradiction with seven. This establishes a
lower bound of nine; the formal result does not assert an exact pair count.

The effect traces are `9/46,4/23,3/23,10/23,3/23,6/23,27/46,14/23,11/23`,
so the counterexample is biased. A separate numerical search reports
candidate unbiased configurations;
these have no exact certificate or Lean proof and do not settle a conjecture
restricted to unbiased MICs.

## Triage

Tier 1 published quant-ph conjecture, preregistered in #11474.
The Scribe theorem node records `Refuted`. The theorem is classified
`proof_shape: bind-only`: finite reconstruction and arithmetic use pinned
Mathlib positivity and rank bounds, with no independent escape witness.
Admission uses `open-problem-resolution`; utility is `certified-instance`
with basis `refutes` the formal `claim`.

### What the settlement shows

- The literal seven-pair bound fails while every MIC requirement is retained:
  the witness is positive semidefinite, rank one, normalized and informationally
  complete, with nine distinct orthogonal cycle pairs. The proposed upper bound
  fails because these pairwise zeros coexist with exact reconstruction of every
  Hermitian operator; the real Hermitian span is not lost.
  [proved: D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.result]

- The failure mechanism is a sparse zero pattern compatible with an invertible
  reconstruction map. For the Route data, all 36 unordered trace products have
  exactly the nine listed zeros: the zero graph is the cycle C9, every degree
  is two, its maximum clique has size two, and the other 27 products are
  strictly positive. Thus there is no mutually orthogonal triple. The coordinate
  matrix B of the unscaled outer products has determinant -46 and rank nine,
  while the positive weights k/46 give the identity sum.
  [computed: `python3`/SymPy exact outer products, all `a < b` trace products,
  clique enumeration and `B.det(), B.rank(), sum(E)`; outputs: zeros=9,
  positive=27, degrees=(2,2,2,2,2,2,2,2,2), clique=2, det(B)=-46, rank(B)=9,
  sum(E)=I3]

- Bias cannot be removed by rescaling these same nine rays while retaining
  the POVM condition. Solving B times the scaling vector equals the coordinates
  of I3 gives the unique solution k/46. Its effect traces are
  `(9/46,4/23,3/23,10/23,3/23,6/23,27/46,14/23,11/23)`.
  Equal-trace normalization `U_a = v_a v_a†/(3 ||v_a||²)` instead has sum with
  diagonal `(91/90,169/180,21/20)` and entry `(0,1)=(-11-i)/90`, rather than I3.
  The nonzero unique scaling coefficients also retain, for this witness, the
  paper's obstruction to rescaling a proper subset into a POVM.
  [computed: `python3`/SymPy `B.inv()*coords(I3)`, effect traces and
  `sum(P/(3*trace(P)))`; outputs: scaling=(3,2,2,4,3,3,9,7,11)/46,
  traces=(9/46,4/23,3/23,10/23,3/23,6/23,27/46,14/23,11/23),
  normalized-sum diagonal=(91/90,169/180,21/20), entry(0,1)=(-11-i)/90]

- Whether every rank-one qutrit MIC with the added equal-trace hypothesis
  `tr(E_a)=1/3` has at most seven orthogonal pairs remains open here. The biased
  witness and the uncertified unbiased numerical candidates do not settle this
  restricted statement. [open]

- Whether nine is the sharp maximum over all rank-one qutrit MICs remains
  open here; a sharpness argument must exclude ten or more unordered orthogonal
  pairs. The certified lower bound alone does not supply that upper bound. [open]

- The witness satisfies the paper's neighbouring tight-frame criterion rather
  than breaking it. With `W` having columns `sqrt(k_a/46) v_a`, its vector Gram
  matrix `g=W†W` is an idempotent of rank three and trace three, and
  `g` Hadamard-multiplied by its complex conjugate is the effect Gram matrix G,
  of rank nine. These checks preserve the criterion for this instance; the
  nine-cycle zeros also preserve the paper's no-orthogonal-basis conclusion
  for this instance.
  [computed: `python3`/SymPy exact `g*g-g`, `g.rank()`, `trace(g)` and
  `g.multiply_elementwise(conjugate(g))`; outputs: g²-g=0, rank(g)=3,
  trace(g)=3, Hadamard product=G, rank(G)=9]

- The paper's seven-pair example remains a valid special case, without being
  a maximum certificate. Its nine printed projector matrices, divided by
  three, sum to I3, each is rank one with trace 1/3, and their Hermitian
  coordinate matrix has rank nine. Their seven zero pairs, using zero-based
  indices, are `(0,1),(0,3),(0,5),(1,2),(1,4),(3,6),(4,6)`.
  [computed: `python3`/SymPy exact printed Example 1 matrices divided by three,
  projector identities, ranks, traces, coordinate rank and all unordered trace
  products; outputs: (3E_a)²=3E_a=(3E_a)† for all nine, sum=I3,
  ranks=(1,1,1,1,1,1,1,1,1), traces=(1/3,1/3,1/3,1/3,1/3,1/3,1/3,1/3,1/3),
  coordinate-rank=9, zero-pairs=((0,1),(0,3),(0,5),(1,2),(1,4),(3,6),(4,6))]

- Further conclusions for the paper's orthocross no-zero question
  (Conjecture 2), its Weyl--Heisenberg spectral plateau question (Conjecture 4),
  and its SIC distance-optimality theorems remain open in this module.
  An orthocross implication needs the orthocross construction hypothesis;
  a plateau implication needs the Weyl--Heisenberg ensemble and spectral
  relation; a distance-optimality comparison needs equal traces and the stated
  matrix norm. The pair-count refutation supplies none of those additional
  results. Conjecture 3's separate inverse-Gram settlement is the result cited
  in Gap, not a consequence of this counterexample. [open]

## ASSUMED-UNVERIFIED

The Preston thesis and Gaussian-noise citing paper recorded as inaccessible
in #11474 remain unverified. The bounded literature check establishes no
exhaustive novelty or priority. Numerical unbiased candidates are uncertified.
The Lean kernel checks the stated predicate and proof, not the authenticity
or version history of the external paper. Template registration of this
refutation is unfinished: the enrolled CounterexampleRecord witness interface
needs separate actual-witness, variation and sensitivity evidence; this
module exposes only the closed refutation and keeps its concrete witness private.
