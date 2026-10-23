---
slug: gibilisco-isola-2004-quantum-cube-root-scalar-curvature
bibkey: gibiliscoisola2005scalarcurvature
doi: 10.1063/1.1834693
url: https://arxiv.org/abs/math-ph/0407007v2
triage: theorem
motivation_gids:
  - D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.result
---

# Quantum cube-root scalar curvature is strictly Schur-increasing

## Problem

Gibilisco and Isola, *On the monotonicity of scalar curvature in classical and quantum information geometry*, arXiv:math-ph/0407007v2, Conjecture 4.2, printed page 11:

> Suppose $n\geq2$. For the function $\mathrm{Scal}_p(\cdot):\mathcal D^1_n\to\mathbb R$ one has the following properties: if $p\in(1,2)$ then $\mathrm{Scal}_p$ is strictly Schur-decreasing; if $p\in(2,+\infty]$ then $\mathrm{Scal}_p$ is strictly Schur-increasing.

This settlement proves the quantum $p=3$ slice, equivalently $\alpha=1/3$, in every dimension $n\ge2$. The faithful density states are positive definite complex Hermitian matrices of trace one. The metric is the Euclidean pull-back of $A\mapsto3A^{1/3}$, with real trace inner product. Scalar curvature is defined by coordinate Christoffel symbols and Ricci contraction, rather than by the spectral formula proved below. The source's order calls $x$ more mixed than $y$ when the decreasingly sorted prefix sums of $x$ are at most those of $y$, with equal total sums.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every dimension $n\ge2$ | `claim` quantifies natural `n` with hypothesis `2 ≤ n`. | Exact. |
| Faithful complex density states | `densityStates` requires `PosDef` and trace one for both matrices; positive definiteness supplies Hermiticity. | Exact. |
| Cube-root pull-back geometry | `HermitianCubeDerivative.alphaEmbed3`, `HermitianDensityCoordinates.rho`, and `metric` give the literal derivative pull-back. `scal3` contracts coordinate curvature at `chartPoint`. | Exact; the fixed trace-one chart is proved equivalent to the Hermitian trace-one space. |
| Eigenvalue majorization | `eig` selects the Hermitian eigenvalue vector; `PositiveSimplexGeometryAndMixing.moreMixed` is the existing decreasing-sort owner. | Exact and independent of permutation order. |
| Schur increase | `result` concludes `scal3 B ≤ scal3 A` when `eig A` is more mixed than `eig B`. | Exact source convention. |
| Strictness outside permutations | The second conjunct concludes `scal3 B < scal3 A` unless the eigenvalue vectors differ by a permutation. | Exact. |
| Other values of $p$ and the decreasing clause | No corresponding conclusion in `claim`. | Open; outside this slice. |

## Motivation

The motivation declaration is `D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.result`. It identifies a quantum curvature quantity that strictly increases under spectral mixing. The tier-3 research line is preregistered in [#15179](https://github.com/the-omega-institute/trureturing/issues/15179). The five content hosts have admission basis `escape-witness`; `HermitianHypersurfaceCalculus` owns the density-coordinate and Gauss support together with the positive cubic derivative, and `HermitianCubeDerivative` owns the smooth inverse and immersion; the Proved resolution metadata records the dossier's conclusion independently of that basis.

## Gap

The source and Gibilisco's 2020 survey, *Lᵖ unit spheres and the α-geometries: questions and perspectives*, Entropy 22, 1409, state the quantum conjecture. The literature screen recorded in #15179 found numerical qubit evidence in Andai's arXiv:math-ph/0604031 and no all-dimension proof of this slice in the searched sources. The citing-paper screen is incomplete and does not certify worldwide priority. The missing mathematical bridge is from intrinsic coordinate curvature to the eigenvalue ratio, together with a strictly positive two-coordinate derivative.

## Route

The Hermitian trace-one chart, the positive cube-map derivative and the smooth local inverse identify the pull-back geometry with the scaled hypersurface $3\{Y>0:\operatorname{Tr}(Y^3)=1\}$. The normal derivative and the coordinate Gauss equation express curvature through the Hermitian Jordan operator. Its real traces yield, for $y_i=\lambda_i^{1/3}$ and $s_k=\sum_i y_i^k$,

$$\mathrm{Scal}_3=\frac{N}{9s_4^2},\qquad N=\bigl((4n^2-2)s_1^2-2ns_2\bigr)s_4-8ns_1s_5+8s_6.$$

`QuantumCubeRootScalarCurvatureMonotone.scal3_eq_spectral_ratio` proves this identification with the coordinate definition. The moment-deficit certificate in `CubeRootSpectralMonotonicity` makes the derivative positive along a strict equalizing T-transform. `CoordinateCurvatureMajorization.spectral_moreMixed_strict` combines it with the existing positive transfer chain, published at its original owner `LogScalarCurvatureMonotone.moreMixed_positive_chain`. No new majorization decomposition is asserted.

The shared `moreMixed`, sorting, prefix sums and T-transform definitions are reused from the frozen owners. The existing simplex coordinate curvature formulas are specific to the logarithmic chart; `EuclideanHypersurfaceGauss` supplies the metric-parametrized formulas needed for the quantum chart. The existing Geometry Library note supplies the paper's bibliographic identity.

## Falsifier

A faithful pair in any dimension $n\ge2$ whose eigenvalues satisfy the source's mixing order but whose cube-root scalar curvatures violate the weak inequality would refute the conclusion. Equality outside a permutation orbit would refute strictness. A discrepancy between the coordinate curvature and the spectral ratio would invalidate the geometric bridge.

## Evidence

The settling theorem is `QuantumCubeRootScalarCurvatureMonotone.result : claim`. Its geometric bridge is `scal3_eq_spectral_ratio`; its spectral strictness theorem is `CoordinateCurvatureMajorization.spectral_moreMixed_strict`. The supporting content includes `HermitianCubeDerivative.positive_hermitian_cube_derivative_equiv`, its smooth cube-root inverse and immersion, and `CubeRootSpectralMonotonicity.Pair.strict_t_transform_any_pair`. The density chart equivalence and the metric-parametrized Gauss contraction are consumed bind-only support in `HermitianHypersurfaceCalculus`. Their axiom closures use only `propext`, `Classical.choice` and `Quot.sound`.

The four-slot escape audit is unfinished under [#15716](https://github.com/the-omega-institute/trureturing/issues/15716), covering 42 new public theorem targets and the separately published owner. DTR reading: `DTR-Unregistered`. The typed source bridge and actual law compile, but the registration lacks a law-violating variation, whole-family slot sensitivity and actual observational dependence. Other targets also lack complete typed family realizations and exact bridges. No Reg file is delivered. These missing registration proofs are separate from the Lean mathematical proofs.

Experiment entry: [docs/reports/gibilisco-isola-2004-quantum-cube-root-scalar-curvature](https://github.com/the-omega-institute/trureturing-experiments/tree/915b5cacd52651484d6b1b54fcbe59a1b733e9bf/docs/reports/gibilisco-isola-2004-quantum-cube-root-scalar-curvature). Command: `python3 check.py`; exit 0; script SHA-256 `c35d2ff2c1426b79f967fdb633ed2ba066749081da8ebbe96c6933e73e838f13`; final reading `bad= 0`. The coordinate curvature agrees with the ratio at one point in dimensions two and three, with $p=2$ controls $3/2$ and $14$. The explicit Gauss evaluation agrees at three sampled points in each dimension two through five. Symbolic checks cover the chain-rule identities at dimensions two through four, the moment-deficit identity with symbolic dimension, and the positivity certificates. The random test finds zero violations among 19,999 nontrivial T-transforms at dimensions two through seven. These finite computations do not prove the uniform theorem.

## Triage

### What the settlement shows

| Claim | Evidence kind and scope |
| --- | --- |
| The coordinate quantum cube-root curvature equals the eigenvalue power-sum ratio above. | Kernel-checked: `QuantumCubeRootScalarCurvatureMonotone.scal3_eq_spectral_ratio`, every faithful state and $n\ge2$. |
| Moment-deficit positivity yields strict increase under a nontrivial equalizing T-transform. | Kernel-checked: `CubeRootSpectralMonotonicity.Pair.strict_t_transform_any_pair`; the positivity certificate is a consumed private part of its proof. |
| Spectral mixing increases curvature, strictly outside permutation orbits. | Kernel-checked: `CoordinateCurvatureMajorization.spectral_moreMixed_monotone`, `spectral_moreMixed_strict`, and `QuantumCubeRootScalarCurvatureMonotone.result`. |
| The one-step strict T-transform inequality applies to positive vectors without normalization. | Kernel-checked: `CubeRootSpectralMonotonicity.Pair.strict_t_transform_any_pair`; the majorization theorems still require the positive simplex, and no singular-state extension is asserted. |
| The listed symbolic and numerical checks have no discrepancy. | Computed: the pinned experiment, with exactly the finite scope stated in Evidence. |
| Other quantum $p$ slices, including the Schur-decreasing clause for $1<p<2$, and singular-state extensions. | Open; this delivery supplies no settling theorem for them. |
| The separate classical logarithmic endpoint $p=\infty$. | Kernel-checked elsewhere: `LogScalarCurvatureMonotone.result`, [#15145](https://github.com/the-omega-institute/trureturing/issues/15145); it is not a quantum endpoint theorem. |
| Consequences for the remaining source conjectures, including Petz and WYD curvature monotonicity. | Open; no implication from the proved $p=3$ slice is asserted. |

The decisive mechanism is the coordinate-to-spectral identity followed by moment-deficit positivity. The theorem has no simple-spectrum restriction: the smooth cube-root inverse covers repeated eigenvalues. Sharp extremal values and boundary curvature are not settled here.

## ASSUMED-UNVERIFIED

The external literature screen and inaccessible proceedings chapters are supplied, bounded evidence from #15179. Unpublished work and exhaustive priority are unverified. The four-slot audit remains unfinished under #15716. Numerical evidence is limited to the experiment's tested instances and does not establish the all-dimension conclusion.
