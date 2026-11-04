---
bibkey: idealintersection2026sixsupport
authors: the-omega-institute/ideal-intersection-laplacian contributors
year: 2026
title: "Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness"
doi: null
url: https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex
claim: "The public source gives the six-support quotient, weighted energy, uniform positive-real low-root theorem, balanced sharpness formula, complete real global spectral separation and endpoint-one isolation with sharpness, supplementary fixed-real-gap endpoint-one expansion, and endpoint equality polynomial."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot
license: citation-only
triage: anchor
---

# Six-support quotient source

## Verified locator

URL: https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex

The pinned file has 52,245 bytes and SHA256
`8553e367c53f71840404e13967395791748a57f1ced4bacf105f36e5fcb477c8`.
The matrix and zero-kernel relations occur on lines 574–600; the
weighted-energy argument on lines 774–784; the symmetric block and
Schur complement on lines 850–913; the uniform-low-root theorem on
lines 915–972; and balanced sharpness on lines 114–145.

The mathematical model and stated results belong to this public source.
The Lean proofs and the exposition in the corresponding Blueprint are
independently authored. The source is cited, not reproduced or treated
as a source-code license. Generic spectral and matrix results are reused
from the pinned Mathlib and repository libraries. No discovery or
priority claim follows from this formalization.

The explicit two-dimensional comparison plane
`(x, sqrt(b)y, sqrt(c)y)` and its completed-square identity are a
repository synthesis of the source's comparison geometry. They replace
its determinant-to-inertia step on the live proof path. The transition
construction likewise completes a square in the positive singleton
coordinate after eliminating the two positive paired diagonals. These
constructions preserve the real domain and the singular boundary
`a = 3`. The generic spectral expansion is supplied by `RHLinalg` and
Mathlib; it is not claimed as new mathematics.

## Endpoint equality polynomial and integer finiteness

The endpoint equality polynomial is in
[paper/sections/endpoint-one-spectrum.tex](https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/sections/endpoint-one-spectrum.tex#L184),
Remark `rem:endpoint-one-equality-curve`, at the same pinned revision.
This file has 11,394 bytes and SHA256
`16c52326f7c88bf538ee2b70bfc4f6c6e4b6901f93d963cd288ab96e4d4c50f5`.
The polynomial on lines 186–190 is the source for the arithmetic
application in the owning Blueprint. Its elementary representative,
bounded-auxiliary-integer and eliminant argument applies existing
polynomial-root and finite-fiber results; it is distinct from the public
source's geometric argument. No novelty claim is made for this application,
and it does not establish the graph/matrix correspondence or the geometric
claims in that remark.

## Global spectral separation and endpoint-one application

The exact public locator at the same revision is
[paper/sections/endpoint-one-spectrum.tex](https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/sections/endpoint-one-spectrum.tex#L8),
`thm:endpoint-one-spectrum`, statement and complete proof through its
sharpness paragraph, lines 8–118. The complete source file has 11,394 bytes,
SHA256 `16c52326f7c88bf538ee2b70bfc4f6c6e4b6901f93d963cd288ab96e4d4c50f5`
and Git blob `b61e5619a508f11c7df335dd468ce61e2aa60000`. These identify
public source, rather than a compiled application proof.

The application uses **every real** `2 ≤ a ≤ b ≤ c`, including repetitions
and boundary values. Its matrix is exactly the existing
`SixSupportLaplacianLowRoot.quotient a b c`, in support order
`1,2,3,12,13,23`, with weights `a,b,c,ab,ac,bc`. Let
`χ_C(X) = det(XI−C)` and let `h_C = χ_C/X` be exact polynomial division;
then `χ_C = X h_C` and the evaluation formula
`h_C(x) = det(xI−C)/x` is used for `x ≠ 0`. In particular
`h_C(1) = det(I−C)`. For its ascending real characteristic roots,
**counted with algebraic multiplicity**, and `s = a+b+c`, the statement is

\[
0=\lambda_1<\lambda_2\le\lambda_3<a+b<s
\le\lambda_4\le\lambda_5\le\lambda_6,
\qquad
\lambda_4=s\ \Longleftrightarrow\ (a,b,c)=(2,2,2).
\]

At the exceptional triple the exact characteristic polynomial and ordered
multiset are

\[
\chi_C(X)=X(X-6)(X^2-12X+12)^2,
\quad
(0,6-2\sqrt6,6-2\sqrt6,6,6+2\sqrt6,6+2\sqrt6).
\]

On `h_C(1) = 0`,

\[
b+c\ge 2a^2-2a+1,
\qquad
b+c=2a^2-2a+1
\ \Longleftrightarrow\
\bigl(b=a\ \text{and}\ c=(a-1)(2a-1)\bigr).
\]

If also `a > κ = 2+√3`, one is **simple** and the **smallest positive**
quotient root. Exact division gives the monic quartic
`R_C = h_C/(X−1)`; its four ascending roots, with algebraic multiplicity,
are `(λ₃,λ₄,λ₅,λ₆)` and satisfy

\[
a<\mu_1<\min\{c,a+b\},\qquad s<\mu_2\le\mu_3\le\mu_4.
\]

Sharpness concerns every real `a ≥ 2` on the **ordered endpoint-one**
family `b=a, c=(a−1)(2a−1)`. The same actual determinant satisfies

\[
h_C(1)=0,\qquad
h_C(a)=a^4(a-1)^2(2a-1)^2(a^2-4a+1).
\]

At `a=κ` the smallest residual root equals `a`. For **every real**
`2 ≤ a < κ`, at least one root of that same exact residual quartic lies
below `a`. Below the cutoff division removes one occurrence of one;
simplicity of one is not assumed in that range.

The complete independently authored proof lives in the existing owning
Blueprint narrative. Its correspondence to the public proof and existing
suppliers is as follows.

| Source clause | Actual binding and proof in the owning narrative |
| --- | --- |
| Actual spectrum and simple zero | `quotient_geometry` gives the exact constant kernel, positive semidefinite `S`, and `S = D C[p,p] D⁻¹`, with positive `D=diag(rootWeights)` and `p=[0,1,2,5,4,3]`. Stored `S` has order `1,2,3,23,13,12`. Characteristic-polynomial transport, Hermitian diagonalization, rank-nullity and reversal of `eigenvalues₀` supply one simple zero and the actual sorted root multiset. |
| Roots below `a+b` | The source block on `3,12,13,23` uses stored selector `[2,5,4,3]`. Its two-dimensional part has `Q(a+b)=−ab(a+b)<0`; its shifted form is `ab(u−ρv/(ab))²−(a+b)v²`, `ρ²=abc`. With scalar shifts `−a,−b` this gives three negative directions and hence at least three actual roots below `a+b`. |
| Roots above `s` | The singleton block of `S−sI` has first pivot `bc−a ≥ a(a−1)>0` and determinant `cΔ`, where `Δ=ab(c−b)+(a−1)(b−a)(b+a)+(a−2)a²`. Its complete nonnegative decomposition vanishes exactly at all two. Off that point real inertia gives at least two roots above `s`. |
| Global count and boundary | The literal determinant yields `h_C(s)=−rsV`, `r=abc`, `p=ab+ac+bc`, `V=r(s+3)−sp=Σ_cyclic a²(bc−b−c)>0` off all two. Thus `3 ≤ N(s) ≤ 4` and the six-factor sign forces exactly three below `s`. At all two, `balanced_sharp_threshold` at `m=2` supplies the full repeated-root factorization above. |
| Endpoint comparison and equality | The same `det(I−C)` normalizes to the exact `q=b+c,z=bc` polynomial in source lines 67–74. The narrative includes every coefficient, the factored comparison to `z₀=a(q−a)`, and the complete positive decomposition of `−B(a,a+u)`, whose constant is at least five for `a≥2,u≥0`. It proves both the lower bound and equality iff, including the family converse. No sign premise or independent `q,z` is assumed. |
| Isolation and residual division | On pair coordinates, `aI−S` is nonpositive. The positive spectral subspace is disjoint from that dimension-three subspace, so `N(a)≤3`, even at repeated parameters. The endpoint bound and `a>κ` imply `h_C(a)=−a²b²c²(a²+2a−b−c)>0`. Zero and one give `N(a)≥2`; even parity forces `N(a)=2`, proving simplicity and identification. The same dimension argument for `S−cI` gives `λ₃≤c`, and `h_C(c)=−a²b²c²(c²+2c−a−b)<0` excludes equality. Exact division removes the simple one. |
| Sharpness for every real parameter | Family ordering follows from `c−a=2a(a−2)+1≥1`; the endpoint factorization proves `h_C(1)=0`. At `κ` the distinct roots `0,1,a` fill the three low positions, so `a` is the smallest residual root. Below `κ`, negative determinant, `2≤N(a)≤3` and parity force three roots below `a` with multiplicity; deleting zero and one occurrence of one leaves a residual root there. |

Here `N(t)` counts the **actual six characteristic roots** below `t`
with multiplicity. The determinant parity step is used only after these
count bounds and exclusion of a root at `t`; determinant signs alone do
not give the theorem. All determinant identities come from a division-free
leaf/triangle expansion of the literal matrix, which is valid also at
`x=a,b,c` and repeated parameters. In particular the endpoint calculation
shares actual algebra with the fixed-gap application, while the latter's
eventual fixed-gap analytic argument supplies none of the missing global
count or equality assertions.

This is an existing-results application, with its full derivation in the
owning narrative and no additional mathematical Lean declaration or
Describe theorem. Existing Describe bindings continue to certify their
stated quotient geometry, low-root and balanced results; their scope does
not expand to this application. No fresh kernel acceptance is asserted.
The direct real inertia and multiset suppliers below specify the source
route; exact current applications and their axiom/dependency closure
remain unverified.

The divisor-window corollary, off-surface generic residual positivity,
equality-curve/genus and equality-spectrum proposition later in the same
public file remain separate mathematics. In particular the equality
family above is not the separate locus `c=b(b+2)−a`. This application
establishes no ideal-graph realization, complete three-prime graph
classification, or literature novelty claim.

## Fixed-real-gap endpoint application

At the same public revision
`b93becea662a746badeadba42fdc3d3eb3db9382`, the direct locators are:

- [The fixed-gap proposition and proof](https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/sections/proof-structure.tex#L99),
  `prop:fixed-gap-expansion`, lines 99–141. The support quotient and
  normalization `h_C(x) = det(xI−C)/x` are specified at lines 11–17.
- [The four endpoint-one cubic coefficients](https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/sections/three-prime-classification.tex#L81),
  in the proof of `lem:endpoint-one-small-gaps`, lines 81–86. Their
  algebraic identity holds for arbitrary real `a,b,c`; the lemma's
  separate unit-bracket conclusion assumes `a ≥ 2` and `d ∈ {1,2}`.
- [The support classes and graph correspondence](https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/sections/graph.tex#L4),
  especially lines 4–28. Finite ideal graphs use positive integer
  exponents; the weighted quotient also makes sense for real parameters.

The proposition states that for every fixed **real** `d ≥ 1` there are
real constants `A_d ≥ 2` and `K_d ≥ 0` such that every **real**
`a ≥ A_d`, with `b = a+d`, has exactly one real endpoint root `c* > b`,
globally on that half-line, and

\[
\left|c^*-\left(2a^2+(2d-3)a-\frac{(d+2)(2d-1)}2
  +\frac{d^2}{2a}+\frac{d^2(d+1)(2d-3)}{4a^2}\right)\right|
\le \frac{K_d}{a^3}.
\]

The owning `SixSupportLaplacianLowRoot` Blueprint narrative preserves the
complete independently authored derivation: the determinant of its literal
six-by-six quotient, all four cubic coefficients, the polynomial scaling
`F(t,y) = t⁸Q_{1/t,d}(y/t²)` for `t ≠ 0`, the real implicit branch through
`(0,2)`, every coefficient through degree four, and the residual identity
`F(t,P(t)) = t⁵R_d(t)`. It takes one constant
`M_d = 1+|R_d(0)|`, obtains the common derivative margin
`|F_y(t,s)−8| ≤ 4`, and applies the existing preconditioned residual
inequality to get `|Y(t)−P(t)| ≤ (M_d/4)|t|⁵`. The same neighborhood
also gives `Q_{a,d}(a+d) < 0`. Two roots below `b`, supplied by strict
signs and the intermediate-value theorem, exhaust the cubic degree
together with `c* > b`, proving global uniqueness. Finally one may take
`A_d = max{2,d+2,2/ε_d}` for the common positive radius `ε_d ≤ 1`, and
`K_d = M_d/4`.

This is application exposition of existing results, rather than a new
Lean theorem represented by the existing Describe bindings. The complete
application has no fresh kernel-verification claim. Its domain includes
all fixed real gaps, with threshold and error constant allowed to depend
on `d`; it asserts no uniformity for growing gaps. The quotient consequence
is supplementary to ideal-graph realization and the full graph
classification, which require their own arguments.

The displayed general formula at `proof-structure.tex:104` gives the
constant `−3/2` when `d = 1`. Thus the full specialization is

\[
c^*=2a^2-a-\frac32+\frac1{2a}-\frac1{2a^2}+O(a^{-3}).
\]

The following prose at lines 144–145 uses `2a²−a−2`, which is the
small-gap bracket anchor `L_1`, not the polynomial part of this full
expansion. The bracket `(L_1,L_1+1)` remains a distinct valid statement.
At `d = 2` the expansion is
`2a²+a−6+2/a+3/a²+O(a⁻³)`, and its constant agrees with the anchor
`L_2 = 2a²+a−6`.

## Direct mathematical suppliers

Repository declarations below are cited at
`6b24b302e37ea2ead041655259d42ef4866d3249`; Mathlib declarations are at
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

- [The actual quotient, weights and support permutation](https://github.com/the-omega-institute/trureturing/blob/6b24b302e37ea2ead041655259d42ef4866d3249/D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.lean)
  supply the six-support object in order `1,2,3,12,13,23`. The existing
  geometry and low-root results are reused without being re-proved.
- [CayleyCoverAnalysis.preconditioned_residual_controls_displacement](https://github.com/the-omega-institute/trureturing/blob/6b24b302e37ea2ead041655259d42ef4866d3249/D5/S3/Quantum/Tomography/CayleyCoverAnalysis.lean#L82)
  supplies `(1−q)‖y−x‖ ≤ ‖C(f(y)−f(x))‖` on a convex set with the
  actual derivative and a uniform operator bound. Here both spaces are
  real, `f(s) = F(t,s)`, `J(s)(r) = F_y(t,s)r`, `C(r) = r/8`,
  `q = 1/2`, `x = P(t)`, and `y = Y(t)` lie in the same closed interval.
  Its derivative and bound hypotheses are verified in the narrative.
- [Matrix.det_apply / det_apply'](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean#L66)
  justify the signed finite-permutation expansion over `ℝ`, without
  invertibility assumptions.
- [The real implicit-function interface](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/ImplicitContDiff.lean#L53)
  supplies `ContDiffAt.implicitFunction`, its base value, eventual
  equation and regularity. The instance has `n = ω ≠ 0`, complete real
  spaces and dependent derivative `8 id`, with inverse `(1/8) id`.
  [Analyticity and smoothness](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/ContDiff/Defs.lean#L973)
  give continuity and the analytic/`C^ω` correspondence;
  [Polynomial.hasDerivAt](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/Deriv/Polynomial.lean#L67)
  gives the polynomial derivative.
- [Polynomial.X_pow_dvd_iff](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Polynomial/Div.lean#L45)
  converts the five zero residual coefficients into the polynomial
  witness `R_d`. [Polynomial.continuousAt](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/Algebra/Polynomial.lean#L58)
  and [Metric.continuousAt_iff](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L872)
  supply uniform neighborhoods for the residual, derivative and signs.
  [ContinuousLinearMap.norm_toSpanSingleton](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Normed/Operator/Bilinear.lean#L472)
  identifies the scalar operator norm used in the derivative margin.
- [Polynomial.tendsto_atBot_of_leadingCoeff_nonpos](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Polynomial/Basic.lean#L80)
  applies to `Q(−X)`, whose degree is three and leading coefficient is
  negative. [intermediate_value_Icc and its reversed version](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/Order/IntermediateValue.lean#L587)
  give the negative and middle roots on the continuous polynomial's
  closed intervals, with strict signs excluding their endpoints.
- [Polynomial.mem_roots and card_le_degree_of_subset_roots](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Polynomial/Roots.lean#L134)
  bound the number of distinct roots. The degree inference uses
  [natDegree_eq_of_le_of_coeff_ne_zero](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Polynomial/Degree/Operations.lean#L68)
  and `A > 0`. [Asymptotics.isBigO_iff](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Asymptotics/Defs.lean#L96)
  expresses the final single eventual norm bound.

## Direct spectral and real inertia suppliers

These repository sources are cited at
`6b24b302e37ea2ead041655259d42ef4866d3249`, and Mathlib at
`56a005855ea17e0b0958f73ec801ae140b0a1679`. They supply existing
mathematical facts, rather than current acceptance of their composition.

- [SixSupportLaplacianLowRoot.quotient_geometry](https://github.com/the-omega-institute/trureturing/blob/6b24b302e37ea2ead041655259d42ef4866d3249/D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.lean#L434)
  requires only `a,b,c>0`. It supplies the literal quotient's energy and
  constant kernel, positive semidefinite `S`, exact positive diagonal
  similarity after `supportPermutation`, and actual-carrier eigenvector
  transport. The application derives positivity from `2≤a≤b≤c`.
  [balanced_sharp_threshold](https://github.com/the-omega-institute/trureturing/blob/6b24b302e37ea2ead041655259d42ef4866d3249/D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.lean#L471)
  requires `m≥1`; its `m=2` factorization supplies the exceptional boundary.
  The existing positive-real low-eigenpair theorem has its original scope
  and is not a substitute for sorted multiplicity counts.
- [RHLinalg.finrank_le_posIndex_of_posDefOn](https://github.com/the-omega-institute/trureturing/blob/6b24b302e37ea2ead041655259d42ef4866d3249/D5/S3/Weil/ZetaLinear/Sylvester.lean#L91)
  bounds a positive subspace's dimension by the positive index of any
  finite Hermitian form over an `RCLike` field, here `ℝ`.
  `posDefOn_range_hermPosPart`, `finrank_range_hermPosPart` and
  `posIndex_eq_max_finrank_posDefOn` in the same source supply a positive
  subspace of exactly that index. Its disjointness from the nonpositive
  pair-coordinate subspace gives the upper counts by
  `Submodule.finrank_add_finrank_le_of_disjoint`. This uses weak signs and
  permits all parameter repetitions.
- [RHLinalg.posIndex_conj_le](https://github.com/the-omega-institute/trureturing/blob/6b24b302e37ea2ead041655259d42ef4866d3249/D5/S3/Weil/ZetaLinear/Inertia.lean#L60)
  takes a finite Hermitian `Q` and any rectangular `B`, with no rank
  assumption, and bounds the index of `Bᴴ Q B` by that of `Q`. Coordinate
  selectors give the actual principal compressions used above.
  [inertia_invariant_of_isUnit_det](https://github.com/the-omega-institute/trureturing/blob/6b24b302e37ea2ead041655259d42ef4866d3249/D5/S3/Weil/Pick/InvertibleHermitianInertiaPullback.lean#L116)
  preserves both indices under an invertible square congruence. Apply it
  to the existing real eigenvector unitary and `tI−S` or `S−tI` to identify
  indices with the actual shifted eigenvalue counts.
- [The pinned Hermitian spectral and root-multiset interface](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Matrix/Spectrum.lean#L59)
  provides `eigenvalues₀_antitone`, `spectral_theorem`, `charpoly_eq`,
  `roots_charpoly_eq_eigenvalues₀`,
  `sort_roots_charpoly_eq_eigenvalues₀` and
  `rank_eq_card_non_zero_eigs`. Reverse its decreasing finite enumeration
  to get the ascending list, keeping the multiset throughout.
  [Characteristic-polynomial transport](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean#L143)
  uses `charpoly_reindex`, `charpoly_units_conj` or the equivalent
  invertible intertwining statement; `eval_charpoly` binds evaluations to
  `det(xI−C)`. Positivity discharges diagonal invertibility.
- [Polynomial division](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Polynomial/Div.lean)
  and [root multiplicities](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Polynomial/Roots.lean)
  support exact removal of `X` and then `X−1`, with `roots_mul` and
  `count_roots` preserving repeated roots. Every evaluated denominator
  used above is nonzero; the polynomial definitions do not rely on
  pointwise division at zero. The finite-permutation determinant
  supplier already cited gives the division-free identities.

The real `RHLinalg` route already suffices; a complex-only repository
Courant–Fischer specialization cannot be silently applied over `ℝ`, and
no new third-party import or general interlacing infrastructure is needed.
For the classical mathematical reference frame, see
[N. J. Higham, Eigenvalue Inequalities for Hermitian Matrices](https://nhigham.com/2021/03/09/eigenvalue-inequalities-for-hermitian-matrices/):
its principal-submatrix inequalities apply to real symmetric matrices
and count ordered eigenvalues with multiplicity. The concrete dimension
and compression instances above specify the existing source route.

## Attribution and rights

The global spectral theorem, endpoint-one sharpness, fixed-gap proposition
and quotient mathematics are attributed to the public source. The readable argument here is independently authored, with
direct use of the cited existing library results; this application makes
no discovery or priority claim.

The pinned [RIGHTS.md](https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/RIGHTS.md)
permits inspection and collaboration and identifies the public preprint at
[Zenodo, DOI 10.5281/zenodo.23134979](https://doi.org/10.5281/zenodo.23134979)
under the deposit's CC BY 4.0 license. It selects no general reuse license
for future joint materials. Citation of those mathematics does not import
joint code, formal proofs or private correspondence.
