---
slug: larotonda-rey-problem-3-13
bibkey: larotonda2023weaklyinvariant
doi: 10.1016/j.laa.2023.08.023
url: https://arxiv.org/abs/2302.05957v1
triage: theorem
motivation_gids:
  - D5/S3/HilbertOperators/LarotondaReyNormingFlatnessRefutation.result
---

# Larotonda–Rey Problem 3.13

## Problem

Gabriel Larotonda and Iván Rey, *Weakly invariant norms: Geometry of spheres in the space of skew-Hermitian matrices*, arXiv:2302.05957v1, Problem 3.13, PDF page 26, ask:

> Does $[N,X_C]=0$ for all $N$ norming $V$ imply that $\|V+s[X,V]\|=\|V\|$ in some interval $|s|<\delta$?

The formal target is the closed ambient-matrix formulation `claim` in `D5/S3/HilbertOperators/LarotondaReyNormingFlatnessRefutation`, using the conventions of [#26538](https://github.com/the-omega-institute/trureturing/issues/26538).

### Statement echo

| Source clause | Lean counterpart | Fidelity and boundary |
| --- | --- | --- |
| Positive finite dimension | Positive natural-number binder in `claim` | Matrices have `Fin n` indices. |
| Definition 2.1: nondegenerate, subadditive, positively homogeneous, Ad-invariant | `IsAdInvariantFinsler` | All four requirements apply on `skewAdjoint`; nonnegativity and zero value at zero are explicit. Ambient values outside that subspace are unrestricted. |
| $\varphi_N(Y)=-\operatorname{tr}(NY)$ | `pairing` | The real part is taken in the ambient matrix expression; on the skew-adjoint space this is the source real pairing. |
| Dual norm is the maximum without modulus | `dualNorm` | The supremum is over real trace-pairing values on the skew-adjoint unit ball. |
| Unit norming functional attaining $F(V)$ | `IsNorming` | Skew-adjoint representing matrix, unit dual norm and attainment. |
| $V=i\sum_jv_jP_j$ with orthogonal spectral projections | `SpectralData` | Every projection field and the decomposition are explicit. Distinct values replace the source decreasing order; reordering leaves the sums unchanged. |
| $X_C=\sum_{j\ne k}P_jXP_k$ | `codiagonal` | The unequal-value test selects the distinct spectral blocks. |
| Every norming $N$ commutes with $X_C$ | Universal commutation hypothesis in `claim` | Quantified over every norming matrix, for every spectral decomposition and skew-adjoint $X$. |
| Some $\delta>0$ gives equality for all $|s|<\delta$ | Existential radius and universal real-step conclusion in `claim` | The commutator is $XV-VX$. |
| No corresponding source restriction | Ambient formulation allows $V=0$ and includes norming/decomposition existence conjuncts | These are the binding formal conventions. The proof uses the nonzero two-dimensional witness, the flatness conjunct and the decomposition provided by the asserted claim. |
| Remark 2.4 rank-one normalization | Absent from `IsAdInvariantFinsler` | The theorem refutes the binding unnormalized ambient formulation. A kernel-checked rank-one normalization or identification with the gauge is not claimed. |

## Motivation

Commutation of every supporting matrix is first-order information at a point. A norm sphere can have quadratic departure from its supporting face, so that first-order annihilation does not force any nontrivial straight segment of constant norm.

## Gap

The source and literature screen are recorded in #26538. The screen includes the arXiv source, later same-author papers, repository results and several settlement indexes. No matching settlement was found in that searched scope. Literature completeness is `ASSUMED-UNVERIFIED`: OpenAlex and Semantic Scholar citation endpoints were blocked, MathDB had no located page, the journal full text was unread, and Fan–Glicksberg (1958) and the attachments of Zenodo records 22990643 and 22990655 were unread in full.

## Route

For two-dimensional complex matrices, write $c(Y)=\operatorname{tr}(Y)/2$ and $R(Y)=Y-c(Y)I$. The proof uses the polar supremum

$$F(Y)=\sup_{0\le q\le1}\frac{(1-q^2)|c(Y)|+2q\|R(Y)\|}{1+q^2+q},$$

where the matrix norm is the Euclidean operator norm. The centered part uses the frozen repository definition `D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence.centeredEffect`.

Take $V=\operatorname{diag}(3i/2,i/2)$ and $X=\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$. The proof establishes $F(V)=1$ and a quadratic upper bound $F(V+eW)\le1+e^2\|W\|^2$ whenever $c(W)=0$. Applying the bound to both signs forces every norming functional at $V$ to annihilate every traceless skew direction. Three explicit traceless test directions then force its representing matrix to be central.

Along $V+s[X,V]$, the central coordinate stays $i$ and the centered operator norm has square $1/4+s^2$. A positive support parameter gives strict norm increase whenever $s\ne0$. The step $s=\delta/2$ contradicts every asserted positive flatness radius.

## Falsifier

The formal settlement fails if the polar supremum violates the Finsler conditions, if the support bound does not force central norming matrices, or if a nonzero commutator-line step fails to increase the norm. The private helpers on the proof of `result` establish these properties for the displayed two-dimensional witness. The source-normalized formulation requires an additional normalization bridge, which is outside this kernel-checked claim.

## Evidence

`D5.S3.HilbertOperators.LarotondaReyNormingFlatnessRefutation.result` proves the literal negation of the closed `claim`. The module has generality `I`, utility `kind=certified-instance` with `basis=refutes`, and admission basis `open-problem-resolution (#26538; Refuted)`. Its chain form is `deposit-uncovered`, with no atom or cover. The Scribe has one `OpenProblemResolutionClaim` with resolution `Refuted`, on `result`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

Experiment entry: [exact gauge calculations](https://github.com/the-omega-institute/trureturing-experiments/tree/87e62bfeeb39619d3a1bfb1c04a82ad22c66c535/docs/reports/larotonda-rey-2023-problem-3-13-norming-commutation-flatness), pinned to commit `87e62bfeeb39619d3a1bfb1c04a82ad22c66c535`. The command `python3 /tmp/op-lr2302p313/r1b/experiment-check.py` exits 0 for the script at that commit. The script SHA-256 is `f7feab60bc4bf9d55c5e29519c0b61eb0c57fe13222bd476cc8069ab8d33775d`. Its exact SymPy calculations give raw gauge $1$ at $V$, radius squared $(4s^2+1)/4$, strict boundary excess $(\sqrt5-1)^2/4$ at $s=1$, raw gauge $(4\sqrt2-\sqrt5)/3$ there, and positive rank-one normalization scale $(1+\sqrt7)/2$. These gauge calculations do not identify the polar supremum with the gauge in Lean.

## Triage

| Target item | Status | Evidence kind and scope |
| --- | --- | --- |
| The exact binding claim is false in dimension two. | proved | Kernel-checked `result`. |
| The witness norm is nondegenerate, subadditive, Ad-invariant and absolutely homogeneous; asymmetry does not cause the failure. | proved | Kernel-checked private helpers `bodyNorm_admissible`, `bodyNorm_smul` and `bodyNorm_eq_zero`, consumed by `result`. |
| At $V$, every norming matrix is central and commutes with every codiagonal part, independently of the spectral decomposition. | proved | Kernel-checked private helper `norming_central` and its use in `result`. |
| The local quadratic bound forces every norming functional to annihilate all traceless skew directions, while every nonzero commutator-line step strictly increases the norm. | proved | Kernel-checked private helpers `bodyNorm_quadratic`, `norming_traceless`, `line_radius` and `line_strict`. |
| Raw gauge $1$ at $V$, radius squared $1/4+s^2$, strict increase at $s=1$, and positive rank-one normalization scale $(1+\sqrt7)/2$. | computed | The pinned experiment entry above, exact SymPy, exit 0; dimension two and the stated symbolic identity and fixed-step test only. Not a Lean polar/gauge identification. |
| The family in every dimension $n\ge2$ and the full compact-body/gauge identification. | open | Neither a delivered kernel theorem nor the experiment establishes these uniform extensions. The dimension-two binding assertion is already refuted. |
| Additional strict-convexity or face-stability assumptions, and the source Theorem 3.11 endpoint-norming criterion. | open | No new theorem on these assertions is delivered. Theorem 3.11 concerns a norming functional at $V+[X,V]$, a distinct hypothesis. |

### What the settlement shows

Proved in this module: central norming matrices and quadratic tangency coexist with strict increase on every nonzero commutator-line step. The first-order support condition therefore does not force a local segment of the sphere in the binding formulation. Absolute homogeneity excludes asymmetry as the mechanism. The nearest surviving condition in the source is the different endpoint-norming criterion of Theorem 3.11; the refutation supplies no counterexample to it. No consequence for another source theorem is asserted beyond rejecting use of the binding Problem 3.13 assertion as a universal premise. The normalized source assertion, a complete polar/gauge bridge and higher-dimensional classification remain open here.

## ASSUMED-UNVERIFIED

Literature-search completeness and worldwide priority remain `ASSUMED-UNVERIFIED`, with the citation and full-text gaps listed in Gap. Gauge/polar identification, a kernel-checked rank-one normalization, higher-dimensional extensions and extra-hypothesis classifications are not established by the delivered theorem.
