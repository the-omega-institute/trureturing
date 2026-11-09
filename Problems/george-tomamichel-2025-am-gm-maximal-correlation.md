---
slug: george-tomamichel-2025-am-gm-maximal-correlation
bibkey: georgetomamichel2025correlation
doi: 10.48550/arXiv.2505.15281
url: https://arxiv.org/abs/2505.15281v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.result
---

# Arithmetic and geometric maximal correlation at one

## Problem

I. George and M. Tomamichel, *A Unified Approach to Quantum Contraction and Correlation Coefficients*, arXiv:2505.15281v3, Section VII, page 66, ask:

> Does there exist a quantum state ρ_AB such that µ_AM(A : B)_ρ < 1 and µ_GM(A : B)_ρ = 1?

The answer is negative. For every positive semidefinite trace-one complex matrix on a product of arbitrary finite index types, $\mu_{\rm GM}=1$ implies $\mu_{\rm AM}=1$. Preregistration: [#19997](https://github.com/the-omega-institute/trureturing/issues/19997).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Finite bipartite quantum state | `claim` quantifies over finite types `a`, `b` and a complex matrix indexed by `a × b`, with positive semidefiniteness and trace one | Includes singular marginals; no fixed dimension |
| Definition 24, equation (54), Hermitian local observables | `correlationValues` uses Hermitian `X`, `Y`, zero marginal expectations and both unit quadratic norms | Full feasible set and absolute joint trace |
| Arithmetic and geometric mean operators, equation (15) | `muAM` and `muGM` use the literal arithmetic sandwich sum and square-root sandwich | Marginals are the literal partial sums; proofs reuse the partial-trace owners |
| Geometric coefficient equals one | The antecedent of `claim` | Exact equality |
| Arithmetic coefficient less than one | `result` proves arithmetic coefficient equals one under the antecedent | Stronger negative answer; no uniform estimate away from one |
| A source maximum | The real supremum of the feasible values | Empty sets have real supremum zero; the proof obtains endpoint attainment on finite dimensional centered unit spheres |

## Motivation

`D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.result` settles the first question in Section VII. The result identifies a perfectly correlated pair of binary projective measurements from the geometric endpoint. Its statement includes arbitrary finite dimensions and singular marginal states.

## Gap

The source leaves the endpoint question open. The literature screen recorded in #19997 reads version 3 and searches for later answers. The probe's literature screen also checks related contraction and tensorization papers and metadata for the ISIT article *Quantum Maximal Correlation Coefficients*, DOI `10.1109/ISIT62367.2026.11654172`; full-paper access for that item is unverified. No published settlement is established in that searched scope. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

Compression to the marginal supports gives faithful marginals and preserves the geometric feasible values. A normalized correlation operator is a contraction whose adjoint composite is similar to a recovery channel. Geometric correlation one supplies a second fixed direction. The faithful fixed-space construction gives a nonzero, nonidentity projection commuting with the state, and recovery transports it to a partner projection. Their marginal probabilities and joint probability equal the same $p\in(0,1)$. Centering each projection and dividing by $\sqrt{p(1-p)}$ gives arithmetic correlation one. The arithmetic Cauchy–Schwarz bound supplies the upper bound.

## Falsifier

A counterexample would be a positive semidefinite trace-one finite matrix with $\mu_{\rm GM}=1$ and $\mu_{\rm AM}<1$, using the literal feasible sets of `correlationValues`. Finite floating-point observations do not certify these exact equalities. The kernel-checked conclusion has the full quantification in `claim`.

## Evidence

### Formal result

The settling declaration is `D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.result`. The supporting fixed-projection construction is `D5.S3.Quantum.FixedPointProjection.Channel.channelCommutingFixedProjection`. The centered endpoint and support-compression statements are consumed helpers in `D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Endpoint` and `.Compression`.

The escape audit is unfinished for the new public theorems and the publicized `D5.S3.Quantum.Information.HedgingMajorityThreshold.trace_retained`: [#22403](https://github.com/the-omega-institute/trureturing/issues/22403). No four-slot registration is claimed complete.

### Numerical experiment

[Pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/ad685151965fa20676ba67a1581d3e0c99701401/docs/reports/george-tomamichel-2025-am-gm-maximal-correlation), script `check.py`, SHA-256 `d56c3a64912a3cec02640ea8d58479f5227bdfb19f9722e7bdcfa513ee71f028`. Running the pinned script with Python 3 exits 0. The measured invocation runs Python 3 on an extracted copy with that immutable script hash.

On 200 random two-qubit states, the maximum measured $\mu_{\rm AM}-\mu_{\rm GM}$ is zero, and all measured geometric coefficients are at most one. On 50 random classical $3\times3$ states, the maximum absolute difference is $2.776\cdot10^{-16}$. Five random two-qubit states have matching printed coefficients for the state and its tensor square. The displayed correlated-block state has both printed coefficients `1.000000000000`. These are finite floating-point readings, separate from the proof.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Evidence and boundary |
| --- | --- | --- |
| Support compression preserves the geometric feasible-value set, including singular marginals | Proved; kernel-checked private statements | `Compression.gmValuesPush` gives the exact set correspondence and `Compression.faithfulBipartiteReduction` constructs the support reduction |
| The normalized geometric endpoint gives a nontrivial commuting fixed projection and a partner with equal marginal and joint probabilities $p\in(0,1)$ | Proved; kernel-checked private statements | `Recovery.faithfulGmProjectionPair` constructs the projection pair; `Shared.faithfulSharedProjections` transports the shared probabilities to the original carriers |
| Centering and scaling by $\sqrt{p(1-p)}$ gives an arithmetic feasible value of one, and the upper bound gives supremum one | Proved; kernel-checked private statement and public result | `Arithmetic.amEndpointFromSharedProjections` constructs the feasible value; `result` combines it with the arithmetic bound |
| The decisive fixed-space mechanism | Proved; kernel-checked supporting theorem | `FixedPointProjection.Channel.channelCommutingFixedProjection` constructs a nontrivial state-commuting projection from a faithful invariant state and fixed-space dimension greater than one |
| The source's second Section VII question | Proved in prose, conditional on the source's coefficient bounds, tensorization and ordering theorems | If $\mu_{\rm AM}(\rho)<1$, the endpoint theorem implies $\mu_{\rm GM}(\rho)<1$. The source's coefficient bounds, geometric tensorization and ordering give $\mu_{\rm AM}(\rho^{\otimes n})\le\mu_{\rm GM}(\rho)<1$ for every positive $n$. Thus the sequence cannot converge to one. Tensorization and this consequence are not new Lean declarations here |
| Numerical ordering, classical equality, tensor-square comparisons and correlated-block endpoint | Computed; pinned experiment | Exactly the finite sample scopes in the experiment entry, exit 0; no exact or uniform claim follows from floating point |
| General tensorization of the arithmetic coefficient | Open | Five tensor-square comparisons do not prove a universal tensorization statement |
| Quantitative separation away from the endpoint and extensions to other means | Open | Outside the exact endpoint theorem |
| Literature completeness | `ASSUMED-UNVERIFIED`; literature reading | The bounded screen in #19997 and the stated related-paper screen do not establish exhaustive coverage |

## ASSUMED-UNVERIFIED

Literature-search completeness and the inaccessible full ISIT article remain unverified. The experiment uses floating-point computations. The escape audit remains unfinished under #22403; its missing realization and sensitivity evidence is separate from the mathematical proof. Quantitative bounds, general arithmetic tensorization and other means remain open.
