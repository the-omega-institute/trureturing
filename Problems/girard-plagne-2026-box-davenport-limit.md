---
slug: girard-plagne-2026-box-davenport-limit
bibkey: girardplagne2026boxes
doi: 10.48550/arXiv.2610.16562
url: https://arxiv.org/abs/2610.16562v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Lattices/GirardPlagneBoxLimit.result
---

# The fixed-support Davenport limit of integer boxes

## Problem

Girard and Plagne, *The Davenport constant of low-dimensional boxes*,
arXiv:2610.16562v1, Section 2, printed page 4, ask:

> It appears tempting to conjecture that for every integer d ≥ 1, the ratio D^(d+1)(⟦−m, m⟧^d)/m^d has a limit when m tends to infinity. This is clear when d = 1, and it follows from Theorems 1 and 5 when d ∈ {2, 3}. However, this problem remains open when d ≥ 4.

Here $D^{(d+1)}$ is the maximal length of a minimal zero-sum sequence
in $\llbracket-m,m\rrbracket^d$ with exactly $d+1$ distinct support vectors.
The result is **Proved** under the literal conventions of preregistration
[#17348](https://github.com/the-omega-institute/trureturing/issues/17348).

### Statement echo

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| Integer box | The coordinatewise absolute-value condition in `CofactorKernel.lengths` | Every coordinate is bounded by the natural radius |
| Minimal zero-sum sequence | `CofactorKernel.IsMinimalZeroSum` | Nonzero sequence, zero total, no nonempty proper zero-sum subsequence |
| Support of size $d+1$ | Support cardinality in `CofactorKernel.lengths` | Exactly $d+1$, not at most |
| Maximal length | `GirardPlagneBoxLimit.D` | Natural supremum of the literal sum-of-multiplicities length set |
| Every positive dimension | `GirardPlagneBoxLimit.claim` and `result` | Every natural $d\ge1$ |
| A limit as the radius tends to infinity | `GirardPlagneBoxLimit.girard_plagne_box_limit` | Natural radii, real ratios, limit $\Delta_d$ |
| Existence of the maximum | The nonemptiness and boundedness conjuncts of `claim` | Every $m\ge1$; makes the supremum the intended maximum |

The box and total are literal expressions; proofs use `Finsupp.degree`
for length. Their correspondence to the preregistered formulas is definitional.
The auxiliary constructions `augment`, `cofactor`, `fromWeights`,
`signMatrix` and `delta` are repository constructions. In particular,
$\Delta_d$ is the finite maximum of $|\det T(V)|$ over Boolean sign matrices,
where $T$ adds a top row of ones.

## Motivation

The identified limit connects an additive minimality problem to the maximal
determinant of a cube simplex in every positive dimension. The one settling
declaration is `D5/S3/Arith/Lattices/GirardPlagneBoxLimit.result`;
`girard_plagne_box_limit` gives its explicit limit value.

## Gap

The literature screen recorded in #17348 covers the source's Sections 1–2,
arXiv:2510.20412 (v1 and v2), arXiv:2601.07950, Girard–Zotova
arXiv:2510.23543, Plagne–Tringali arXiv:1405.4363 and arXiv:2610.14546.
No settlement was located in that screen. Sturmfels's monograph, Chapters
6–7, was not obtained. The screen is attributed to the orchestrator and
the reasoning and formalization seats, as recorded in the preregistration;
its completeness is `ASSUMED-UNVERIFIED`.

## Route

`CofactorKernel.sequence_cofactor_length` gives the determinant/length/gcd
identity. `sequence_cofactor_multiplicities` obtains the individual primitive
multiplicities. `CubeSimplexDeterminant.augmented_det_integer_box_bound`
bounds the augmented determinant by $\Delta_dm^d$.

For deficient rank, `MinimalKernelPacking.minimal_kernel_rank_deficient_bound`
deletes a kernel-preserving row and applies floor-weight packing. Its bound
for $d+1$ support vectors is
$(d+1)(2(d+1)m+1)^{d-1}$, which is lower order than $m^d$.

`PrimitivePencil.primitive_pencil_perturbation` constructs one integer matrix
$B$ for which every integer pencil parameter has maximal-minor gcd one.
`CubeSimplexDeterminant.exists_maximizing_sign_simplex` supplies the extremal
simplex; the settling module's private `interiorSimplex_positive_kernel` and
`exists_asymptotic_lower_family` construct strict positive kernels approaching
that maximum. The private `D_lower_eventually` and `D_upper_eventually`
establish the two inequalities used by `girard_plagne_box_limit`.

## Falsifier

A positive dimension and radii for which the fixed-support normalized maximum
does not tend to $\Delta_d$, or a nonempty unbounded length set at one positive
radius, would contradict the formal statement. Definition fidelity therefore
includes exact support cardinality, pointwise subsequence order, all proper
subsequences, and the natural-to-real casts in the ratio.

## Evidence

The Lean modules are `CofactorKernel`, `CubeSimplexDeterminant`,
`PrimitivePencil`, `MinimalKernelPacking` and `GirardPlagneBoxLimit`, all
under `D5/S3/Arith/Lattices/`, with one Blueprint Scribe per module.
The settling Scribe attaches one Proved `OpenProblemResolutionClaim` to
`GirardPlagneBoxLimit.result`.

The four-slot escape audit is unfinished for the public theorems, including
the settling result. [Issue #17570](https://github.com/the-omega-institute/trureturing/issues/17570)
lists the targets and missing source realization, reconstruction,
observational-dependence and sensitivity evidence. No successful registration
is asserted by this dossier.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Evidence and boundary |
| --- | --- | --- |
| Full-rank minimal sequences are primitive positive kernels; their multiplicities and length are absolute cofactors and augmented determinant divided by the cofactor gcd | Proved, kernel-checked | `CofactorKernel.sequence_cofactor_multiplicities`, with `sequence_cofactor_length` |
| The vertex bound caps the determinant by $\Delta_dm^d$ | Proved, kernel-checked | `CubeSimplexDeterminant.augmented_det_integer_box_bound` |
| Rank-deficient supports have lower-order length | Proved, kernel-checked | `MinimalKernelPacking.minimal_kernel_rank_deficient_bound` and private `GirardPlagneBoxLimit.lower_degree_ratio_limit` |
| Primitive pencils realize the leading constant asymptotically | Proved, kernel-checked | `PrimitivePencil.primitive_pencil_perturbation` and private `GirardPlagneBoxLimit.exists_asymptotic_lower_family` |
| The limit is $\Delta_d$ for every $d\ge1$ | Proved, kernel-checked | `GirardPlagneBoxLimit.girard_plagne_box_limit` |
| The length set is nonempty and bounded for every $m\ge1$ | Proved, kernel-checked | `GirardPlagneBoxLimit.result`, with private `lengths_nonempty` and `lengths_bddAbove` |
| The source's $d=1,2,3$ leading constants agree with this formula | Computed | Experiment below gives $\Delta_1=2$, $\Delta_2=4$, $\Delta_3=16$; substitution in the proved limit agrees with the interval case, Theorem 1 in dimension 2, and the leading constant in Theorem 3 and Theorem 5 in dimension 3; no exact higher-dimensional formula follows |
| General values of $\Delta_d$ | Open | The augmented sign-matrix maximal-determinant problem is not evaluated in general |
| Unrestricted box Davenport constants | Open | arXiv:2510.20412 concerns unrestricted support, outside this theorem |
| Exact non-asymptotic values for $d\ge4$ | Open | Convergence determines the leading constant, not exact values |
| Numerical checks | Computed | The single experiment entry below states the complete tested scope |
| Literature status | Literature reading; completeness `ASSUMED-UNVERIFIED` | The bounded screen and unavailable monograph are stated under Gap |

The decisive mechanism is primitive cofactor normalization plus the cube
vertex bound, with a separate lower-order estimate for deficient rank and
a single perturbation primitive at every integer parameter. Its dimension
parameter is unrestricted above; it makes no assertion about unrestricted
support or exact higher-dimensional maxima. The source's lower-dimensional
asymptotic statements are consistent specializations. No additional result
of the source is identified here as depending on the formerly open assertion.

### Experiment

[Pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/73c308cec1a907b063b6e7a614083b5f71b0b0d8/docs/reports/girard-plagne-2026-box-davenport-limit).
Command, from that repository: `python3 docs/reports/girard-plagne-2026-box-davenport-limit/check.py`;
exit 0, `ALL_OK`. Script SHA-256:
`94291f19d14913886f357a5e8d364f36d1ac02fd602cb34bbae46d37030c2fea`.

The exact computations cover $d=2$, $m=2,\ldots,6$, with fixed-support
maxima $13,34,61,98,139$; $d=1$, $m=1,\ldots,12$, with value $2$ at
$m=1$ and $2m-1$ for $m\ge2$; and sign maxima $2,4,16,48$ in dimensions
$1,2,3,4$. The kernel checks cover all $360$ positive-kernel supports in
$[-2,2]^2$. Pencil checks cover $18$ random full-rank matrices in dimensions
$2,3,4$ and integer $t=-15,\ldots,15$. The asymptotic-family checks cover
$d=2,3$, $n=2,4$, at the script's five parameters through $10^5$.
These finite computations do not prove a uniform extension; the universal
limit is established separately by the Lean theorems.

## ASSUMED-UNVERIFIED

Literature completeness and priority are not established. The unavailable
Sturmfels chapters and any sources outside the stated screen remain unchecked.
Numerical checks have only their enumerated finite scope. Four-slot escape
registration remains unfinished under #17570; the Lean proof and its axiom
closure do not by themselves supply registration evidence.
