---
slug: han-zhang-zhang-2026-cycle-six-strong-two-resistance-refutation
bibkey: han2026resistant
doi: null
url: https://arxiv.org/abs/2606.08561v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.result
---

# The six-cycle graph state is not strongly 2-resistant

## Problem

Han, Zhang and Zhang, arXiv:2606.08561v1, page 8, Discussion, ask:

> Several open problems remain. First, do C₅ and C₆ give strongly m-resistant graph states for m = 1 and m = 2, respectively? Here, “strong” means genuine multipartite entanglement rather than mere entanglement.

This dossier concerns the C₆, m = 2 clause. On qubits 0,...,5 its graph-state
amplitudes are (-1) raised to the sum of the six cyclic edge products, divided
by 8. Definition 2 of arXiv:2505.06567v1 requires initial genuine multipartite
entanglement (GME), GME after every two-qubit loss, and full separability after
every three-qubit loss. GME excludes a finite convex mixture of products
across nontrivial bipartitions. The formal claim is
`IsStrongResistant 2 (cycleGraphState 6)`; `result` proves its negation.

## Motivation

The external Tier-1 question and its exact refutation were preregistered in
#11502. The frozen declaration
`D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.result`
answers the C₆ clause No by exhibiting a two-qubit loss whose marginal is
biseparable. The separate C₅ clause is open here.

## Gap

The literature check in #11502 reports arXiv v1 as the only version,
zero citing records in the inspected Semantic Scholar and INSPIRE queries,
and no matching MathDB problem. These are orchestrator- or search-seat
reported readings, not a new literature census by this implementation seat.
The source labels the question open; the source's ordinary-resistance data
do not certify strong resistance. Repository and pinned-Mathlib searches for
the target name and conclusion shape found no previous settlement in their
stated scope. No worldwide priority or exhaustive literature coverage is claimed.

## Route

Take the loss set J = {0,2}. Write its bits t,u and the retained bits r,x,y,z
on qubits 1,3,4,5. The six-cycle phase is
(t+u)r + xy + yz + ux + tz. For each of the four traced configurations, set
`a_tu(r) = (-1)^((t+u)r)` and
`b_tu(x,y,z) = (-1)^(xy+yz+ux+tz)`.

The partial trace is the sum of the four products
`(1/4) (a_tu a_tu* / 2) tensor (b_tu b_tu* / 8)`.
Rank-one positivity and the cardinalities 2 and 8 make both factors
density matrices. The weights are nonnegative and sum to one. The cut
{1} | {3,4,5} is nontrivial, so this is a biseparable decomposition.

## Falsifier

Strong 2-resistance requires GME for every loss set of cardinality two.
The explicit J = {0,2} has that cardinality, and the displayed decomposition
violates this requirement. Its entrywise factorization, positivity,
trace-one conditions, nontrivial cut and convex weights are all checked
within the proof of `result`; no numerical approximation supplies them.

## Evidence

The sole public theorem is
`D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.result : ¬ claim`.
Its proof constructs the four factors and the configuration equivalence
locally. The public definitions use the existing `DensityState` carrier and
`partialTraceFirst`; the frozen record gives their declaration identities
and axiom closures. `result` uses only Classical.choice, Quot.sound and propext.
The Scribe resolution claim records Refuted for this dossier.

## Triage

The C₆ strong-2-resistance clause is refuted. The delivery uses
`admission_basis: open-problem-resolution`, with `proof_shape: bind-only`
and no escape witness. It adds no atom or coverage edge. Escape audit is
unfinished: #11591 identifies the missing faithful enrolled realization;
no Reg registration is claimed.

### What the settlement shows

- Proved in this module, inside `result`: losing qubits 0 and 2 leaves a
  convex combination of four products across {1} | {3,4,5}. Thus universal
  two-qubit-loss GME fails, which refutes the conjunction defining strong
  2-resistance.
- Proved in this module, inside `result`: the four product factors remain
  positive semidefinite and trace one, and their nonnegative weights sum to
  one. The obstruction is genuine multipartite entanglement, not validity
  of the density matrices or normalization of the mixture.
- Open here: the marginal's ordinary entanglement, a kernel verification of
  ordinary 2-resistance, the initial state's GME and the universal
  three-qubit-loss full-separability condition. Refuting one conjunct does
  not separately refute these neighbouring assertions.
- Open here: the C₅, m = 1 clause and independent verification of the paper's
  other results. This refutation concerns the separate Discussion question;
  it supplies no refutation of the source's ordinary-resistance results.

## ASSUMED-UNVERIFIED

The Lean kernel verifies the formal statement, not the external publication,
source quotations or completeness of literature coverage. Fidelity of the
finite-dimensional density-matrix encoding to the published definitions is
a semantic review obligation. The delivery does not settle C₅, other cycle
sizes, ordinary resistance or all loss patterns individually. The escape
audit remains unfinished under the linked issue.
