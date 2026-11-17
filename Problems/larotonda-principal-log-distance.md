---
slug: larotonda-principal-log-distance
bibkey: larotonda2026shortcurves
doi: 10.48550/arXiv.2610.31535
url: https://arxiv.org/abs/2610.31535v1
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.result
---

# Larotonda principal-log distance conjecture

## Problem

Gabriel Larotonda, *Short curves in homogeneous spaces of the unitary group for unitarily invariant norms*, arXiv:2610.31535v1, Section 4.1 after Proposition 4.3, writes:

> It would be natural to conjecture that $d(1,e^z)=\|z\|$ whenever $\|z\|_\infty\le\pi$.

The target is the literal universal assertion encoded by `D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.claim`: for every positive dimension, every matrix-valued extension of a normalized Ad-invariant Finsler norm on the skew-adjoint subspace, and every admissible skew-adjoint $z$ with operator norm at most $\pi$, the directed rectifiable distance from $1$ to $e^z$ equals the norm of $z$. The norm is allowed to be nonsymmetric, and the competitors include every piecewise smooth unitary curve.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $d(1,e^z)=\|z\|$ | `rectifiableDistance F 1 (NormedSpace.exp z) = ENNReal.ofReal (F z)` | The directed infimum and extended nonnegative integral preserve the source's distance and length semantics. |
| $\|z\|_\infty\le\pi$ | `‖Matrix.toEuclideanCLM z‖ ≤ Real.pi` | The operator norm is the Euclidean complex matrix operator norm used by the source. |
| Ad-invariant Finsler norm on $\mathfrak u(n)$ | `IsAdInvariantFinsler F` | Subadditivity, nondegeneracy, nonnegative homogeneity, conjugation invariance and spectral domination are stated on `skewAdjoint`; off-subspace values are unconstrained. |
| Every positive dimension | `∀ n : ℕ, 0 < n` | The natural-number quantifier and positivity hypothesis are explicit. |

## Motivation

The source's stronger unitarily invariant theorem does not cover all Ad-invariant norms on $\mathfrak u(n)$. A trace-coupled quadratic norm preserves conjugation invariance but changes under winding shifts that leave the exponential endpoint fixed. The resulting two-dimensional witness supplies a strict shorter competitor for the claimed principal logarithm.

## Gap

The preregistration is GitHub issue [#26384](https://github.com/the-omega-institute/trureturing/issues/26384). Its literature screen found no matching settlement in the recorded scope. Citation-list completeness, worldwide priority, the absence of a journal version, and the unread full texts of Seco–San Martin (DOI 10.1016/j.difgeo.2017.10.003) and Sakai remain `ASSUMED-UNVERIFIED`.

## Route

Use the literal quadratic norm

$$F(z)^2=\sum_{i,j}\lVert z_{ij}\rVert^2+4\lVert\operatorname{trace}(z)\rVert^2$$

on the skew-adjoint matrices. For the diagonal angles $(4\pi/5,\pi/2)$ and $(-6\pi/5,\pi/2)$, diagonal exponential periodicity gives the same endpoint. The exponential curve of the shifted angle has constant left logarithmic derivative and therefore provides a distance upper bound. The winding identity gives a strict decrease of the quadratic norm, contradicting the claimed equality.

## Falsifier

The settlement would fail if the displayed quadratic norm were not admissible, if the winding shift changed the exponential endpoint, if the witness violated the spectral bound, or if the shifted curve did not give a strict length saving. The delivered declarations establish each of these obligations for the two-dimensional witness.

## Evidence

`D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.result` proves the complete negation of `claim`. Its axiom closure is contained in `{propext, Classical.choice, Quot.sound}`. The Scribe result node carries one `OpenProblemResolutionClaim` with resolution `Refuted` for this dossier. The module uses `deposit-uncovered` with no atom or cover; its admission basis is `open-problem-resolution (#26384; Refuted)`, its generality is `I`, and its utility is the certified-instance refutation of `claim` by `result`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The two published helper theorems `D5.S3.Quantum.Matrix.CommutatorGap.rectNorm_sq` and `D5.S3.Quantum.Matrix.CommutatorGap.rectNorm_sq_square` have unfinished escape audits tracked by [#26905](https://github.com/the-omega-institute/trureturing/issues/26905); no `declared_validated` status is claimed without the required CI current-job readings. The module comment records the same unfinished audit.

Experiment entry: [larotonda-2026-ad-invariant-principal-log-distance](https://github.com/the-omega-institute/trureturing-experiments/tree/3ff99ec15aa771875714ccb1a3a59ca8f0c482e1/docs/reports/larotonda-2026-ad-invariant-principal-log-distance), pinned to commit `3ff99ec15aa771875714ccb1a3a59ca8f0c482e1`. The command `python3 check.py > check.out` exits 0 and ends with `ALL_CHECKS_OK`; `check.py` has SHA-256 `4fd0c0a408d3aa2c3c2876e675c8cf2dcd58fa4df2eb3f0b8620f36c3b2988a1`. The script checks the exact two- and three-dimensional squared values, the winding identity and parameter branches, a nontrivial unitary conjugation, 56 exact family tests in dimensions 2 through 8, and the explicit curve endpoints, derivative and length. These finite checks do not replace the kernel proof or assert the exact global distance.

## Triage

| Target item | Status | Evidence |
| --- | --- | --- |
| The universal conjecture is false in dimension two for the displayed admissible quadratic norm; the $c=4$ trace coupling permits a winding shift with the same exponential and a strictly shorter smooth curve. | proved | Kernel-checked `result` and its consumed admissibility, endpoint, curve-length and strictness helpers. |
| For the specified two-dimensional witness the squared values are $153\pi^2/20$ and $73\pi^2/20$, and the principal spectral norm is $4\pi/5$. | computed | The pinned experiment command above, exit 0, exact rational arithmetic. |
| The $n=3$, $c=4$ witness has spectral norm $9\pi/20<\pi/2$ and squared values $1249\pi^2/200$ and $1089\pi^2/200$; the checker also covers 56 exact family tests in dimensions 2 through 8. | computed | The pinned experiment command above, exit 0, with the stated dimensions and exact scopes. No additional Lean theorem is claimed. |
| Principal-log minimality survives for the stronger unitarily invariant class. | proved | Larotonda, Antezana and Varela, arXiv:1107.2439, Theorem 4.3, read in the primary text; this is literature evidence, not a new declaration here. |
| Local minimizing segments survive inside an appropriate ball in the chosen Finsler norm where exp is a diffeomorphism; this is not a universal spectral-radius $\pi$ or $\pi/2$ statement. | proved | Larotonda–Rey, arXiv:2511.09699v2, Corollary 2.17, primary-text reading of the explicit minimizing-segment statement. |
| The exact global distance for this witness, a sharp safe spectral radius for each dimension and norm, and a full classification of admissible norms with principal-log minimality are not settled here. | open | No delivered declaration or cited computation supplies these uniform conclusions. |
| Extending the source quotient argument to all Ad-invariant norms needs an alternative to the refuted principal-log input; the established stronger-norm quotient theorem is not refuted. | open | The delivered counterexample removes the universal principal-log premise while preserving the literature's stronger-class theorem. |

### What the settlement shows

The failure mechanism is the trace coupling: conjugation preserves the trace term, while an integer winding shift preserves the exponential and changes the trace. The nearest surviving statements are the stronger unitarily invariant principal-log theorem and the local Finsler-ball minimizing-segment result. Proposition 4.3 and the source quotient theorem under stronger unitarily invariant hypotheses are not refuted. The exact global distance and any uniform classification remain open.

## ASSUMED-UNVERIFIED

Literature completeness, worldwide priority, citation-list completeness, the absence of a journal version, and the full-text status of the two unread works named in Gap are `ASSUMED-UNVERIFIED`. The experiment is finite and exact over its stated scopes; any extension beyond those scopes is open.
