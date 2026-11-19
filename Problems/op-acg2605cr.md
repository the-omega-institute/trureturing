---
slug: op-acg2605cr
bibkey: assumpcaocoutinhogodsil2026totalconformal
doi: 10.48550/arXiv.2605.08508
url: https://arxiv.org/abs/2605.08508v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.result
---

# Two-conformal rigidity does not imply one-conformal rigidity

## Problem

Assumpção, Coutinho and Godsil, *Total Conformal Rigidity in Graphs*, arXiv:2605.08508v2, Section 9, printed page 20, ask:

> Are there graphs that are 2-conformally rigid but not 1-conformally rigid?

Definition 1.2 uses the unnormalized weighted Laplacian of a finite simple connected undirected graph, with each undirected edge counted once. Its admissible weights satisfy $w_e\ge0$ and $\sum_e w_e=|E|$. In increasing spectral order, $s_k$ sums indices $2,\ldots,k+1$ and $S_k$ sums the largest $k$ eigenvalues, with multiplicity. Only the mandatory first zero is excluded, so additional zeros remain in $s_k$. Both inequalities are attained at the same all-ones weighting. Preregistration: [#26026](https://github.com/the-omega-institute/trureturing/issues/26026).

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Some finite graph | Existential natural order and `SimpleGraph (Fin n)` in `claim` |
| Simple, undirected, connected, with an edge | `SimpleGraph`, `G.Connected`, and the existential adjacent pair |
| Every undirected edge once | `Edge`, the increasing-endpoint adjacent-pair subtype |
| Closed simplex, normalized to edge count | `ValidWeight`, including zero weights |
| Equation (1), the weighted Laplacian | Endpoint differences and their weighted products expanded literally in `eigenvalue` |
| Increasing eigenvalues, with multiplicity | Hermitian `eigenvalues₀` with reversed bounded index |
| Smallest nontrivial sum | `smallestSum`, indices 1 through $k$ in zero-based order |
| Largest sum | `largestSum`, cutoff $n\le i+k$ |
| Both extrema at uniform weights | `KConformallyRigid`, with independent universally quantified weights |
| Two-rigid but not one-rigid | The two conjuncts in `claim`; `result` proves their existential conjunction |

No source clause is dropped. The edge representation and finite index casts select coordinates without restricting graphs or weights. The literal endpoint expression is related inside consumed private proofs to the existing weighted-Laplacian and incidence-vector owners; no duplicate public Laplacian definition is introduced.

## Motivation

The settling declaration is `D5.S3.Combinatorics.SpectralGraph.TotalConformalRigidityTwoNotOne.result`. The module has `generality: I`, `utility: none`, and `admission_basis: open-problem-resolution (#26026; Proved)`. The proof is classified bind-only after inlining its consumed helpers and stopping at pinned upstream and frozen owners; no independent escape witness is claimed. The external named problem supplies the settlement admission basis.

## Gap

An all-order family beyond the five-vertex witness is open here. The other Section 9 questions about long initial rigidity prefixes and a linear-fraction threshold are unresolved. Upper three-conformal non-rigidity for this same witness is computed below; no separate Lean theorem asserting it is delivered.

## Route

Take $K_5$ with edge $\{0,1\}$ removed. The graph has nine edges and universal vertex 2. Its uniform increasing spectrum is $[0,3,5,5,5]$. A real symmetric certificate $X$ has decreasing spectrum $[8/9,5/9,5/9,0,0]$ and edge quadratic value $10/9$ on each edge. Thus every normalized weighted Laplacian $L(w)$ satisfies $\operatorname{tr}(L(w)X)=10$.

The consumed `RHLinalg.vonNeumann_trace_ineq` bounds this trace pairing by the spectral pairing. Eigenvalue order and rational normalization give an upper bound by the two largest eigenvalues of any real Hermitian five-by-five tested matrix. Positivity of $L(w)$ and its trace 18 then give $s_2(w)\le8$ and $S_2(w)\ge10$. Uniform weights attain both constants.

Assign $6/5$ to the six edges meeting $\{0,1\}$ and $3/5$ to the other three. This positive weighting has total nine and increasing spectrum $[0,18/5,21/5,21/5,6]$. Its second eigenvalue exceeds the uniform value 3, disproving one-conformal rigidity of the witness.

## Falsifier

A mismatch between the source's closed simplex and the quantified weights, omission of boundary weights or extra zero eigenvalues, or failure of the stated trace certificate would invalidate the correspondence. The kernel-checked result uses the full closed simplex. Replacing the unnormalized Laplacian by a normalized Laplacian changes the problem.

## Evidence

The settling Lean module and its consumed private helpers are `D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.lean`. Its Scribe displays the complete claim on `result` and carries one Proved resolution claim for this dossier. The source note is `Library/Eigenstructure/assumpcaocoutinhogodsil2026totalconformal.md`.

The reused `D5.S3.StatisticalMechanics.BoseSelectionFixedOrthogonalBaths.increasingSpectrum_of_charpoly` identifies a monotone real root vector with the Hermitian increasing spectrum. Its statement and proof are preserved; it is published for the private diagonalization adapter used by the certificate and both graph spectra.

Four-slot escape registration for `result` and the published characteristic-polynomial owner is unfinished in [#30083](https://github.com/the-omega-institute/trureturing/issues/30083). Missing evidence comprises faithful source observations and source selection, actual-positive and rejected-intervention laws, whole-family sensitivity and actual observational dependence. No retained Reg mirror or `declared_validated` status is claimed.

### Exact certificate computation

Experiment source: [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/fdb14d54aeebf9b7662b36c41cbaa8114b19ad4c/docs/reports/assumpcao-coutinho-godsil-2026-two-not-one-conformal-rigidity).
The immutable `check.py` has SHA-256 `4cec6067801c7b1c0cb982866ecb6f65d9955beb2fe0b67c8d663ea2ad017b5b`. Command `python3 /tmp/op-acg2605cr/stageb/experiment.py` executes those exact bytes and exits 0. It checks the nine-edge five-vertex graph, the uniform and specified perturbed spectra, the spectra of $X$, $I-X$ and $Y$, symbolic trace/edge identities in all nine weights and an arbitrary symmetric test matrix, and all nine vertices of the weight simplex. Its final result is `ALL_CHECKS_OK`. These computations support exactly that scope and do not establish the universal theorem by enumeration.

## Triage

### What the settlement shows

| Item | Status | Evidence |
| --- | --- | --- |
| $K_5$ minus one edge is connected, has nine edges, is two-conformally rigid and is not one-conformally rigid | Proved | Kernel-checked `result`, `graph_connected`, `edge_card`, `graph_two_rigid`, `graph_not_one_rigid`; private names are in the settling module. |
| $s_2(w)\le8$ and $S_2(w)\ge10$ for every admissible weighting, including every boundary weighting; uniform weights attain both | Proved | Kernel-checked `all_weights_bounds`, `uniform_eigenvalues`, `graph_two_rigid`. Nonnegativity permits zero. |
| Constant edge quadratic trace mechanism; the trace estimate applies to every real Hermitian five-by-five tested matrix without a positive-semidefinite hypothesis on that matrix | Proved | Kernel-checked `lap_X_trace` and `trace_certificate_bound`; the latter's telescope assumes only Hermitian symmetry. |
| Positive orbit weights $6/5$ on six cross edges and $3/5$ on three clique edges have spectrum $[0,18/5,21/5,21/5,6]$ and second eigenvalue greater than 3 | Proved | Kernel-checked `perturbed_valid`, `perturbed_eigenvalues`, `uniform_eigenvalues`, `graph_not_one_rigid`. |
| The same weighting violates the upper $k=3$ rigidity inequality: top-three sum $72/5<15$ | Computed | Exact spectra computed by the pinned command in Evidence; $6+21/5+21/5=72/5$ and the uniform top-three sum is $5+5+5=15$. This neighbouring non-rigidity statement has no separate delivered Lean theorem. |
| All-order witness family, long initial rigidity prefixes and a linear-fraction threshold | Open | No declaration or computation here settles these broader questions. |

The decisive mechanism provides uniform control over a continuum of real weights, rather than a bounded enumeration of weightings. The tested-matrix trace bound needs no positivity hypothesis; positivity is used for the weighted-Laplacian lower spectral bound. No inspected source result relies on an affirmative answer to the Section 9 question as an established premise. No change to the scope of the source's other results is claimed.

### Literature status

The bounded source and literature screen in #26026 identifies the question in version 2 and finds no exact settlement in its completed scope. It includes the related papers arXiv:2605.15017, arXiv:2506.20541 and arXiv:2505.10548v5, later author works and bounded repository/index searches. The standard spectral inequality is reused, not claimed as new. Literature completeness is ASSUMED-UNVERIFIED; this is a formal settlement of the named question without a worldwide priority claim.

## ASSUMED-UNVERIFIED

Literature completeness, unindexed settlements, full citing-work enumeration and the unavailable thesis/full-text search are ASSUMED-UNVERIFIED. The preregistration records Semantic Scholar rate limits and unsuccessful true arXiv full-text searches. The unfinished escape evidence is specified in #30083. Computations cover the exact finite and symbolic checks described in Evidence; no uniform all-order extension is inferred.
