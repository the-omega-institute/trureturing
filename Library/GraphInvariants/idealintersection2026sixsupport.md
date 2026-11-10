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

## Exact actual matrix and characteristic-polynomial correspondence

The complete matrix correspondence concerns the existing LowRoot carrier
itself. In support order `1,2,3,12,13,23`, write
`C(a,b,c) = SixSupportLaplacianLowRoot.quotient a b c`. It is the literal
matrix

\[
\begin{pmatrix}
 b+c+bc&-b&-c&0&0&-bc\\
 -a&a+c+ac&-c&0&-ac&0\\
 -a&-b&a+b+ab&-ab&0&0\\
 0&0&-c&c&0&0\\
 0&-b&0&0&b&0\\
 -a&0&0&0&0&a
\end{pmatrix}.
\]

The support weights are `a,b,c,ab,ac,bc`. The negative off-diagonal entries
are the D−A convention: every displayed interaction has the negative target
weight. This is the actual quotient, including its nonsymmetric carrier; the
symmetric representative used by the existing geometry is only a proved
similar carrier for real positive parameters.

The same literal matrix is defined over every commutative ring `R`. The
universal integer model uses `ℤ[x₀,x₁,x₂]` and the rational model uses
`ℚ[x₀,x₁,x₂]`. Coefficientwise specialization to any commutative ring, and to
every `ℚ`-algebra for the rational model, returns the actual matrix. The maps
commute with the matrix, its characteristic polynomial and the exact `divX`
operation. Integer, rational and arbitrary-parameter readings are therefore
coefficient extensions of one matrix definition.

Write `χ_C(X)` for the characteristic polynomial and `h_C(X)` for
`χ_C.divX`. The constant coefficient of `χ_C` is zero because the all-one
vector is an exact kernel vector over every commutative ring. Exact polynomial
division gives

\[
\chi_C(X)=Xh_C(X),
\]

with zero remainder. `divX` is this polynomial quotient; it is not pointwise
division at `X=0`. Over a nontrivial coefficient ring the six-by-six
characteristic polynomial has degree six and `h_C` has degree five. These
facts make no positivity, ordering, simplicity or root-index assumption.

For every parameter triple, the same carrier gives
`h_C(1)=det(I−C)`. On the endpoint substitution put

\[
t=b(b+2),\qquad q=a(t-a),\qquad A=3b-1,
\]
\[
B=b(b^2+4b-1),\qquad
C_0=-(b^2+2b-1)(b^2+3b-1)(b^3+3b^2+3b-1),
\]

and

\[
G(a,b)=Aq^2+Bq+C_0.
\]

The literal determinant calculation over the universal ring, followed by
coefficient extension, gives for all commutative-ring parameters

\[
h_{C(a,b,t-a)}(1)=-(b-1)G(a,b).
\]

The factor `b−1` is retained; no cancellation is performed. This identity is
the endpoint specialization of the actual matrix characteristic polynomial,
not merely the quartic's defining equation.

Regard `G` as a polynomial in `a` over `ℚ[b]`. Its `a`-degree is exactly four.
As a polynomial in independent `a,b`, its total degree is exactly seven and the
coefficient of `a^0 b^7` is `−1`. These are coefficient identities for the
actual endpoint polynomial, before any field or geometric interpretation.

For real `a,b`, the actual matrix has spectral value one exactly on

\[
1\in\operatorname{spec}_{\mathbb R} C(a,b,t-a)
\quad\Longleftrightarrow\quad b=1\ \text{or}\ G(a,b)=0.
\]

The `b=1` component is genuine and remains present for every real `a`. This
is an algebraic spectrum equivalence. It does not infer an ordered root index,
simplicity, positivity, or the hypotheses of the separate ordered real
spectral theorem.

### Literal bridge to the quartic tower

The endpoint polynomial above is coefficientwise the `actualQuartic` used in
the characteristic-zero tower. After mapping `ℚ[b]` into `k[b]` and then
`K = RatFunc k`, the resulting polynomial in the fresh quartic parameter variable `X`,
representing `a`, is the literal

\[
g(X)=AX^4-2AtX^3+(At^2-B)X^2+BtX+C_0.
\]

In the actual fields `H=K(y)` with `y^2=D` and `F=H(z)` with `z^2=f`, choose
`a=(t+z)/2`. The recovery identities are

\[
q=a(t-a),\qquad y=2Aq+B,\qquad z=2a-t.
\]

They prove directly that the endpoint polynomial evaluated at this tower
generator is zero and that the generator is the same root of the literal `g`.
The quartic quotient `K[X]/(g) ≃ F`, its residue-root map and the coefficient
extension are consequently bridges between the actual matrix endpoint
expression and the actual field tower. They are derived from the displayed
definitions and recovery equations, rather than inferred from declaration
names.

The matrix identities, universal/rational specializations, degree facts,
endpoint factor, coefficient and spectrum assertions are supplied by the
complete source-bound matrix proof. This is readable application exposition;
it adds no retained Lean, Reg, Describe, freeze or positive-certificate
declaration. The existing global real spectrum and fixed-gap applications
remain in force. Smooth proper models, local branches and uniformizers,
genus and Riemann–Hurwitz, geometric finiteness interfaces, graph realization
and full classification remain separately owed.

## Exact quartic algebra over characteristic-zero fields

The equality-curve remark rem:endpoint-one-equality-curve in
paper/sections/endpoint-one-spectrum.tex at public revision
b93becea662a746badeadba42fdc3d3eb3db9382 supplies the polynomial used here.
Its linked curve note at revision 8ed4f9014f6142949e6af40fd16e18ca304f629a
supplies the displayed discriminant and norm numerator. The polynomial and
those parameters are attributed to that source. The following derivation is an
application of existing integral-closure, quadratic-algebra, Kummer,
minimal-polynomial and Gauss results, not a novelty claim. The existing
Describe statements retain their stated quotient geometry, low-root and
balanced scope; this application adds no Lean declaration or Describe theorem.

Let k be any field of characteristic zero, let b be an indeterminate, and put
K = k(b), represented by RatFunc k. Map rational coefficients into k[b] and
then into K; these maps are injective. We keep the same letters for the
images. No algebraic-closedness assumption on k is needed for the field-tower
argument. In this section C₀ is the scalar constant coefficient, distinct from
the six-support matrix C; the owning Blueprint's [`IntegerFiniteness()` section](../../Blueprint/D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.scribe.cs) denotes this
same scalar by C. Define the literal polynomials

\[
t=b(b+2),\qquad A=3b-1,\qquad B=b(b^2+4b-1),
\]

\[
C_0=-(b^2+2b-1)(b^2+3b-1)(b^3+3b^2+3b-1),
\]

\[
D=12b^8+92b^7+233b^6+172b^5-154b^4-172b^3+161b^2-44b+4,
\]

\[
N=(b^3+5b^2+6b-2)(3b^6+8b^5-6b^4-36b^3-28b^2+40b-8).
\]

For the plane variable a, write q = a(t−a). The polynomial is quartic in a,
with coefficients in k[b]:

\[
G(a,b)=A[a(t-a)]^2+B[a(t-a)]+C_0.
\]

Exact polynomial identities and branch prerequisites. Polynomial normalization
gives both identities below. The degrees of D and N are eight and nine; a
prime denotes differentiation in b. Explicit rational Bézout identities for
(D,D′), (N,N′) and (N,D) give their normalized gcds equal to one; mapping each
Bézout equality into k[b] preserves coprimality. Thus D and N are squarefree,
and their root sets are disjoint in an algebraic closure. These are exact
identities for these polynomials, rather than assumed squarefreeness or norm
certificates.

\[
B^2-4AC_0=D,\qquad At^4+4Bt^2+16C_0=N.
\]

\[
\gcd(D,D')=\gcd(N,N')=\gcd(N,D)=1.
\]

For explicit Bézout witnesses, a coefficient list (c₀,…,cₘ) denotes the
polynomial Σᵢ cᵢbⁱ, in ascending powers of b. The following rational
coefficient lists satisfy U_D D+V_D D′ = 1, U_N N+V_N N′ = 1 and U_ND N+V_ND D
= 1, respectively. These identities can be read as polynomial equalities
before mapping to k[b].

U_D = (15077458503622003/12603918688, -54128905348874963/12603918688,
-6246087705771407/3150979672, 117940112961877943/12603918688,
145006858328612117/12603918688, 30779539539563445/6301959344,
551481433980327/787744918).

V_D = (1370677759331121/12603918688, -19934798047738501/25207837376,
36019683710933693/25207837376, 8204653143188935/12603918688,
-44366105575549787/25207837376, -47526676857220537/25207837376,
-1093986370835811/1575489836, -551481433980327/6301959344).

U_N = (-1551720656793517/69254786592, 290115890479151/46169857728,
6813283610138383/92339715456, 34122483667637429/554038292736,
3370077294694969/2216153170944, -86652849207243331/4432306341888,
-39894848329397747/4432306341888, -417181352926057/328318988288).

V_N = (-1551724985217679/554038292736, 13284078298392293/1108076585472,
-27151801510553/123119620608, -13019587671423695/738717723648,
-1608792935985931/130361951232, -192340276236565/492478482432,
2030298571254023/738717723648, 9931651975121645/8864612683776,
417181352926057/2954870894592).

U_ND = (-3559310030328403/471932176, 6462996085656055/117983044,
-46657822536661549/471932176, -21303192533434097/471932176,
14356909865819141/117983044, 61549445215520121/471932176,
5667971824526075/117983044, 714366125043951/117983044).

V_ND = (889827514956041/29495761, -3793513481796410/29495761,
61458663986279/29495761, 22274907297181941/117983044,
15611438025308693/117983044, 249440883003581/58991522,
-13899098543371799/471932176, -5667971824526075/471932176,
-714366125043951/471932176).

At r = 1/3 the exact values are A(r) = 0, A′(r) = 3, B(r) = 4/27, D(r) =
16/729 and N(r) = 368/729. The nonzero rational values remain nonzero in every
characteristic-zero k. The gcds and these values are prerequisites for the
later branch analysis; they do not identify any local ring or ramification
point on a model.

The first actual quadratic field. Coprimality with D′ makes D separable, hence
squarefree, after coefficient extension. If x² = D in K, the integral-closure
result IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow, applied to
the polynomial ring k[b] and its fraction field K, supplies a polynomial w
whose image is x. Injectivity then gives D = w² in k[b]. Squarefreeness forces
w to be a unit, which would make D a unit of degree zero, contrary to degree
eight. Thus D is nonsquare in K, with this premise proved for the displayed D.

The existing QuadraticAlgebra field instance therefore constructs the field H
= QuadraticAlgebra K D 0, with generator y = omega satisfying y² = D. Its
basis 1,y and finrank_eq_two give [H:K] = 2, and adjoin_omega_eq_top gives H =
K(y). The prime-two instance of
Polynomial.X_pow_sub_C_irreducible_iff_of_prime shows X²−D is irreducible;
minpoly.eq_of_irreducible_of_monic identifies it as minpoly_K(y). The
polynomial A has leading coefficient 3 ≠ 0, so its image in K and then H is
nonzero and invertible. Define

\[
q=\frac{y-B}{2A},\qquad f=t^2-4q=t^2+\frac{2B}{A}-\frac{2y}{A}.
\]

Using y² = D and B²−4AC₀ = D gives Aq²+Bq+C₀ = 0 and y = 2Aq+B. Here q is an
actual element of H, and y = 2Aq+B puts its generator in K(q), so H = K(q).
The first quadratic conjugation fixes K and sends y to −y. Its norm
calculation is

\[
\operatorname{Norm}_{H/K}(f)=\left(t^2+\frac{2B}{A}\right)^2-\frac{4D}{A^2}=\frac{At^4+4Bt^2+16C_0}{A}=\frac{N}{A}.
\]

QuadraticAlgebra.norm_def supplies the expression u²−Dv² for u+vy.
QuadraticAlgebra.det_toLinearMap_eq_norm, together with Algebra.norm_apply,
identifies that expression with the actual field norm Algebra.norm K on H.
Therefore its multiplicativity is available for the nonsquare inference,
rather than being an unproved norm interpretation.

A proved simple rational-field pole. Since A = 3(b−r) and N(r) ≠ 0, the
reduced monic RatFunc denominator of N/A is exactly b−r, with root
multiplicity one. The denominator-divisibility, cross-multiplication and
monicity results for RatFunc give this reduced-denominator statement. N/A is
nonsquare by a direct algebraic obstruction: if x² = N/A in K, then (Ax)² =
AN. The same integral-closure supplier gives w in k[b] with w² = AN.
Evaluation at r forces w(r) = 0. Differentiating the polynomial identity and
evaluating at r would force 0 = A′(r)N(r) = 3·368/729, which is nonzero in
characteristic zero. This proves the simple-pole nonsquare without assuming a
valuation certificate. It concerns the rational base field; it does not yet
prove orders at either of the two places of H over r.

The second actual quadratic field. If f were a square in H, multiplicativity
of the actual field norm would make N/A a square in K. Thus f is nonsquare.
The existing field instance now constructs F = QuadraticAlgebra H f 0 = H(z),
with z = omega, z² = f, [F:H] = 2 and minpoly_H(z) = X²−f. The Kummer
irreducibility and generation suppliers apply with the proved f-nonsquare
premise, just as at the first step. Module.finrank_mul_finrank on the actual
scalar tower gives [F:K] = 4. Both quadratic steps and F/K are finite
separable extensions: all the fields have characteristic zero, and their
finite algebraic extensions are separable. No smooth model or full
constant-field assertion is used to obtain these field-level statements.

The actual quartic generator. In F choose a = (t+z)/2, using the embeddings K
→ H → F consistently. The sign of y is fixed by q = (y−B)/(2A). The equations
z² = f and Aq²+Bq+C₀ = 0 give the recovery identities

\[
q=a(t-a),\qquad y=2Aa(t-a)+B,\qquad z=2a-t.
\]

Every element of H is h₀+h₁y with h₀,h₁ in K, and every element of F is u+vz
with u,v in H, by QuadraticAlgebra.re_smul_add_im_smul. The recovery formulas
put y and z in K(a); these decompositions then put all of H and F in K(a).
Hence F = K(a) = k(b,a), with a genuinely generating the field already
constructed. Field.primitive_element_iff_minpoly_natDegree_eq gives degree
four for minpoly_K(a).

To bind that generator to the literal polynomial, let X be a fresh polynomial
variable and put g(X) = A[X(t−X)]²+B[X(t−X)]+C₀ in K[X]. Its expansion is

\[
g(X)=AX^4-2AtX^3+(At^2-B)X^2+BtX+C_0.
\]

Thus g has degree four and leading coefficient A ≠ 0, and the actual a
satisfies g(a) = 0. Its monic normalization A⁻¹g has the same degree and
vanishes at a, so minpoly.unique_of_degree_le_degree_minpoly gives A⁻¹g =
minpoly_K(a). Irreducibility of the minimal polynomial and multiplication by
the nonzero constant A give irreducibility of g in K[X]. The argument uses
this original g throughout.

The root-preserving polynomial quotient. Because g and A⁻¹g are associated,
AdjoinRoot.algEquivOfAssociated identifies their quotients;
AdjoinRoot.algEquivOfEq then uses A⁻¹g = minpoly_K(a). The existing
minpoly.equivAdjoin and the proved generation identify the latter quotient
with all of F. The composite is a K-algebra equivalence K[X]/(g) =
AdjoinRoot(g) ≃ F, sending the residue root to the chosen a. The recovery
formulas above identify y and z in its image as well. This supplies the actual
quartic-polynomial/field correspondence, separately from the
matrix/characteristic-polynomial correspondence.

Primitivity and absolute polynomial irreducibility. Work first in k[b][X],
before passing to its fraction field in b. The polynomial A is a nonzero
scalar multiple of b−1/3, while B(1/3) = 4/27 ≠ 0, so A and B are coprime in
k[b]. A divisor common to all coefficients of G divides the coefficients A of
X⁴ and At²−B of X²; it therefore divides B and is a unit. This proves that the
literal quartic is primitive.
Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map now
transfers the proved irreducibility in K[X] back to k[b][X].

For coefficient extension, let G_ℚ denote precisely A[X(t−X)]²+B[X(t−X)]+C₀ in
ℚ[b][X]. The coefficientwise homomorphism pk : ℚ[b] → k[b], induced by ℚ → k,
sends G_ℚ to exactly the plane polynomial just used; its further map to K[X]
is g. Consequently the original rational polynomial remains irreducible after
this coefficient extension for every characteristic-zero k. In particular,
taking k = AlgebraicClosure ℚ proves irreducibility of map(pk)(G_ℚ) in
(AlgebraicClosure ℚ)[b][X]. This is the actual absolute polynomial
irreducibility statement, rather than only irreducibility over ℚ(b). It
supplies no smooth projective model or genus computation.

Second conjugation and fixed elements. The involution of the second quadratic
algebra fixes H and sends z to −z, so it sends a to t−a and fixes q = a(t−a)
and y = 2Aq+B. For u = u₀+u₁z with u₀,u₁ in H, conjugation gives u₀−u₁z. Since
2 ≠ 0 and 1,z are independent, it fixes u exactly when u₁ = 0, exactly when u
is in the image of H in F. This identifies the field fixed elements with H. It
does not construct a quotient morphism between smooth models.

Supplier correspondence. The applications above use Mathlib revision
56a005855ea17e0b0958f73ec801ae140b0a1679:
IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow for both nonsquare
obstructions; QuadraticAlgebra's field instance, finrank_eq_two,
omega_mul_omega_eq_algebraMap, re_smul_add_im_smul, adjoin_omega_eq_top,
norm_def and det_toLinearMap_eq_norm for the actual fields, generators,
degrees, norm and conjugation; Polynomial.X_pow_sub_C_irreducible_iff_of_prime
and minpoly.eq_of_irreducible_of_monic for the two quadratic minimal
polynomials; Module.finrank_mul_finrank and
Field.primitive_element_iff_minpoly_natDegree_eq for the degree-four
generator; minpoly.unique_of_degree_le_degree_minpoly, minpoly.equivAdjoin and
AdjoinRoot.algEquivOfAssociated/algEquivOfEq for its minimal polynomial and
quotient; and
Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map for Gauss
transfer. The owning Library note gives direct public source locators. These
are existing suppliers applied to the displayed parameters; this exposition
retains no named transient checking wrappers or positive-instance
declarations.

Remaining E3 boundary. The exact E3.00 universal six-support
polynomial/characteristic-polynomial bridge, exact X division, substitution
c = b(b+2)−a, identity h_C(1) = −(b−1)G, and faithful matrix
correspondence are supplied in the preceding matrix section. The literal
quartic quotient equivalence is separately tied to that bridge there. The
algebra portions of E3.01–E3.02 and E3.06–E3.08 are the discriminant, both
actual fields, norm, nonsquares, degrees, separability, primitive generator
and absolute polynomial irreducibility established above; their actual
curve/model identifications remain separate.

E3.03 still requires actual smooth proper models, full constant fields,
identification of their function fields and actual finite separable b-maps.
E3.04 must identify the eight finite D-branch places and both infinity places
with local rings, uniformizers, ramification and different hypotheses. E3.05
must apply Riemann–Hurwitz on that quotient model to obtain 2g(H)−2 = 2(−2)+8
= 4 and genus three. Squarefree degree eight alone is not that model-level
proof.

E3.09 still requires nine actual simple f-zero places above roots of N, with
regularity of both conjugate factors, a nonzero companion and order one. E3.10
must identify both H-places over 1/3, proving q and f have order −1 at one and
that the other has q regular and f nonzero, with the local norm/order bridge.
E3.11 must supply the two actual infinity points and coordinates giving ord(q)
= −3 and ord(f) = −4 at each. E3.12 must exclude all other odd valuations,
discharge local Kummer parity and tame different hypotheses, and prove exactly
ten branches. The rational-field simple pole above is not a substitute for
these local assertions.

E3.13 still requires the actual smooth projective normalization, its full
constants and model morphism, and matched Riemann–Hurwitz with 2g(X)−2 =
2(2·3−2)+10 = 18, giving geometric genus ten. Arithmetic genus fifteen is not
substituted. For E3.14 the elementary all-integer finiteness application in
the owning Blueprint's [`IntegerFiniteness()` section](../../Blueprint/D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.scribe.cs) already supplies finiteness of G(a,b) = 0, including
A(b) ≠ 0 on integer b and finite a-fibers; this algebra section does not erase
or reprove that result. The separate geometric route still owes an actual
integer map to the constructed smooth affine quotient, its at-most-two fibers,
and a Siegel or complete hyperelliptic finiteness theorem with all hypotheses
matched. The F1–F3, G1–G5, E1–E4 and original 21+5 obligations are unchanged.
No complete E3, effective point list, emptiness or graph classification
follows from the algebra application alone.

### Direct algebra suppliers

All Mathlib links below are fixed at
`56a005855ea17e0b0958f73ec801ae140b0a1679`, the supplier revision for
this algebra application.

- [Integral closure](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean#L252):
  `IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow` applies to
  `R = k[b]`, `K = RatFunc k` and exponent two. The actual polynomial
  square supplies integrality in each of the two nonsquare arguments.
- [Quadratic-algebra construction, conjugation and norm](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/QuadraticAlgebra/Basic.lean#L607):
  the field instance takes the no-root condition, furnished here by
  the proved nonsquares with second parameter zero. The same source's
  `omega_mul_omega_eq_algebraMap`, `re_smul_add_im_smul`,
  `adjoin_omega_eq_top`, `norm_def` and `im_star` give the actual equations,
  generation, norm expression and fixed-elements calculation.
  [The quadratic basis and finrank](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/QuadraticAlgebra/Defs.lean#L405)
  supply `finrank_eq_two` at each step.
- [The norm determinant identification](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/QuadraticAlgebra/NormDeterminant.lean#L27)
  is `QuadraticAlgebra.det_toLinearMap_eq_norm`; composed with
  `Algebra.norm_apply`, it binds the computed quadratic expression to
  the multiplicative field norm used in the f-nonsquare inference.
- [Kummer irreducibility](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/FieldTheory/KummerPolynomial.lean#L124)
  is `Polynomial.X_pow_sub_C_irreducible_iff_of_prime` at prime two,
  with the two already discharged nonsquare premises.
  [Minimal-polynomial uniqueness](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/FieldTheory/Minpoly/Field.lean#L62)
  is `minpoly.unique_of_degree_le_degree_minpoly`; the monic quartic has
  the same degree as the generator's minimal polynomial and vanishes at it.
- [Primitive-element dimension](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/FieldTheory/PrimitiveElement.lean#L372)
  is `Field.primitive_element_iff_minpoly_natDegree_eq`. Its input here is
  the proved equality `K(a) = F`, with finite dimension four from the tower.
- [Root-preserving AdjoinRoot equivalences](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/AdjoinRoot.lean#L488)
  give `AdjoinRoot.algEquivOfAssociated` and `AdjoinRoot.algEquivOfEq`.
  Their residue-root formulas, followed by
  [minpoly.equivAdjoin](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/FieldTheory/Minpoly/IsIntegrallyClosed.lean#L211)
  and generation, give the explicit image a, rather than only an abstract
  field isomorphism of degree four.
- [Gauss's lemma for primitive polynomials](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Polynomial/GaussLemma.lean#L258)
  is `Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map`.
  It applies over `k[b]` with fraction field `RatFunc k`, after the
  coefficient-divisor argument using A and B. The final specialization
  uses `k = AlgebraicClosure ℚ`, not just k = ℚ.
- [Reduced rational-function denominators](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/FieldTheory/RatFunc/AsPolynomial.lean)
  supply `RatFunc.num_mul_eq_mul_denom_iff`, `denom_div_dvd` and
  `monic_denom`; `Polynomial.rootMultiplicity_X_sub_C_self` identifies
  the simple root of the resulting denominator. Characteristic-zero
  [Algebra.IsSeparable.of_integral](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/FieldTheory/Separable.lean#L663)
  supplies the algebraic-field separability assertions, independently
  of the still required full-constant-field and model statements.

The public parameter locator is the
[curve note](https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/8ed4f9014f6142949e6af40fd16e18ca304f629a/notes/endpoint-one-equality-curve.md),
linked by the pinned equality-curve remark. Its geometric conclusions
remain attributed to that source; the model, local and genus obligations
listed above are not discharged by this polynomial/field application.

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
route. The accepted F/G exact applications retain their PR25764 status.
The additional source-bound E1/E2/E4 transient applications and their recorded
dependencies are described in “Evidence scope and the remaining geometric
frontier”; its independent entire-native review 36807 is complete with three approve
verdicts at that batch’s recorded evidence scope. This candidate’s whole-source review
and canonical delivery remain owed.

The divisor-window corollary, off-surface generic residual positivity,
and equality-curve/genus remain separate mathematics. The exact
equality-spectrum locus `c=b(b+2)−a` is supplied in the section
“Exact actual matrix and characteristic-polynomial correspondence”; the endpoint family above is a
different real equality family. This application establishes no
ideal-graph realization, complete three-prime graph classification, or
literature novelty claim.

## The actual residual quartic and its strict coefficient window

Keep the literal C = SixSupportLaplacianLowRoot.quotient a b c in support order 1,2,3,12,13,23.
Write χ_C for its characteristic polynomial and h_C = χ_C.divX, so χ_C(X) = X h_C(X) by exact
monic division. For positive parameters, the positive diagonal similarity and support
permutation above identify its complete characteristic-root multiset with that of the existing
real symmetric S. In this section and the next two, the symbols A,B,D,N and F refer to the
residual quartic coefficients and polynomial; they are distinct from the coefficients,
discriminant, norm numerator and field F in the equality-curve tower.

For arbitrary real a,b,c, put s = a+b+c, p = ab+ac+bc and r = abc. Define A = p+3s−1, B =
sr+2sp+3s²−3s+1, D = r²+(s²−s+1)r+s²p+p²+(s−1)³, and N = rs(p+s). The explicit monic quartic is
F(X) = X⁴−AX³+BX²−DX+N. These coefficient definitions carry no endpoint or ordering assumption.

The division-free leaf/triangle determinant identity for the literal quotient gives h_C(X) = X
h_C(1)+(X−1)F(X), for every real parameter triple. Evaluation gives h_C(x) = x h_C(1)+(x−1)F(x)
for every real x, including x = 1. Differentiating the polynomial identity and evaluating at
one gives F(1) = h_C′(1)−h_C(1). These are polynomial equalities, with no division by x−1. On
h_C(1) = 0, exact monic division identifies F with h_C/(X−1). Outside that surface F need not
be this monic-division quotient and its roots are not identified with quotient roots.

Now consider any ordered real triple 4 ≤ a ≤ b ≤ c with actual h_C(1) = 0. Since 4 > 2+sqrt(3),
the full endpoint-isolation application supplies the four actual residual roots μ₁,…,μ₄ with
algebraic multiplicity. With U = min{c,a+b}, they satisfy a < μ₁ < U and s < μ₂ ≤ μ₃ ≤ μ₄. Thus
F(X) = ∏ᵢ₌₁⁴(X−μᵢ), its root multiset is {μ₁,μ₂,μ₃,μ₄}, and χ_C(X) = X(X−1)F(X). In particular
det(xI−C) = x(x−1)F(x) for every real x, including zero and one. The complete quotient-root
multiset is {0,1,μ₁,μ₂,μ₃,μ₄}; zero, one and μ₁ each have algebraic multiplicity one, since μ₁
< a+b < s < μ₂; repeated high residual roots are permitted.

Comparing coefficients of this actual split product gives every Vieta identity: Σᵢ μᵢ = A, Σᵢ<ⱼ
μᵢμⱼ = B, Σᵢ<ⱼ<ₖ μᵢμⱼμₖ = D and μ₁μ₂μ₃μ₄ = N. All four roots are positive. Dividing the third
identity by the nonzero product gives D/N = 1/μ₁+1/μ₂+1/μ₃+1/μ₄. This argument retains
multiplicities throughout.

Set R = 2/s+1/(A−U−2s). Before taking reciprocals, s,p,r,N are positive, and p > U+1: indeed ac
≥ 4c and ab,bc ≥ 16 imply p > c+1 ≥ U+1. Therefore A−U−2s = p+s−1−U > s > 0, and 0 < R < 3/s.
Also s/r = 1/(ab)+1/(ac)+1/(bc) ≤ 3/16, so 3r ≥ 16s and r > 4s. Finally 2(s²−3p) =
(a−b)²+(a−c)²+(b−c)² ≥ 0, and s−1 > 0.

Expansion of the displayed coefficients gives D−3N/s = r(r−4s)+r(s²−3p+1)+s²p+p²+(s−1)³ > 0.
Every term is nonnegative and the first term is strictly positive. Since N > 0 and R < 3/s, it
follows that D−NR > D−3N/s > 0 and D > 0. Thus s, all μᵢ, A−U−2s, N, D and D−NR are positive;
every reciprocal and quotient used in the window has a justified positive denominator.

For x,y > s > 0, the exact scalar identity 1/s+1/(x+y−s)−1/x−1/y = (x−s)(y−s)(x+y)/(sxy(x+y−s))
has a strictly positive right side. Apply it to μ₂,μ₃, and then to μ₂+μ₃−s,μ₄. It gives 0 < H =
1/μ₂+1/μ₃+1/μ₄ < 2/s+1/(μ₂+μ₃+μ₄−2s). The Vieta sum and μ₁ < U give μ₂+μ₃+μ₄−2s = A−μ₁−2s >
A−U−2s > 0, so H < R. Strictness comes from μ₂,μ₃,μ₄ > s and permits equality between high
roots.

Now D/N = 1/μ₁+H and 0 < H < R imply (D−NR)/N < 1/μ₁ < D/N. Inverting positive quantities and
combining with a < μ₁ < U yields the exact strict window max{a,N/D} < μ₁ < min{U,N/(D−NR)}.
Both bounds are strict on the entire stated real domain; neither the endpoints nor the ordering
hypotheses have been dropped.

For the arithmetic specialization assume a,b,c are integers with 4 ≤ a ≤ b ≤ c and actual
h_C(1) = 0 after injection into the reals. Form the same literal six-by-six matrix C_ℤ over ℤ,
and F_ℤ = (χ_Cℤ /ₘ X) /ₘ (X−1). Entrywise integer-to-real injection sends C_ℤ to C.
Characteristic polynomials commute with this map, as do both divisions by the monic X and X−1.
Hence F_ℤ maps to the actual F. Injectivity transfers monicity, degree four and the exact
factorization χ_Cℤ = X(X−1)F_ℤ, and its constant coefficient is N_ℤ =
abc(a+b+c)(ab+ac+bc+a+b+c). The first division is exact from the kernel; the endpoint
hypothesis makes the second exact.

If d is an integer whose real image is the smallest actual residual root μ₁, then F_ℤ(d) = 0 by
the injective coefficient map. Polynomial.IsRoot.dvd_coeff_zero gives d dividing N_ℤ, and μ₁ >
a ≥ 4 gives d > 0. That d obeys max{a,N/D} < d < min{U,N/(D−NR)}, with the coefficients and
fractions evaluated in the reals. Separately, each of the other three residual roots that is an
integer is at least a+b+c+1, since it is strictly greater than the integer s. No assumption
that all four roots are integers is needed. Divisibility and these windows are necessary
conditions only: they assert no converse, sufficiency, splitting criterion, finite enumeration
or unbounded exclusion.

The coefficient-window mathematics is attributed to the endpoint-one corollary in
paper/sections/endpoint-one-spectrum.tex at b93becea662a746badeadba42fdc3d3eb3db9382 and the
total-sum note at 4a451ac51055c6d04926967749196f12ac8e49c8. The written argument follows the
actual endpoint quartic, full G isolation, coefficient comparison and two strict reciprocal
merges supplied by the completed transient applications. Their evidence scope is stated after
these three sections; the existing Describe bindings retain their original statements.

## Closed residual positivity for arbitrary unsorted parameters

For every unsorted real triple a,b,c ≥ 8 and every x in the closed interval 0 ≤ x ≤ 4, the
explicit generic quartic F above satisfies F(x) > 0. No endpoint, parity, upper-size or
parameter-ordering hypothesis enters this positivity statement. Its off-surface polynomial
identity and continuation at x = 1 are the actual determinant identities established in the
preceding section.

Define the homogeneous expression J(a,b,c;v,w) =
256v⁴−64Av³(v+w)+16Bv²(v+w)²−4Dv(v+w)³+N(v+w)⁴, using the same A,B,D,N at a,b,c. For each row
(i,j,k) in the complete table below, let (g₀,g₁,g₂,g₃,g₄) be its five entries and put
P(m,t,u;v,w) = Σ_rows mⁱtʲuᵏ Σ_ell=0⁴ g_ell v^ell w^(4−ell). The full coefficient identity is
J(8+m,8+m+t,8+m+t+u;v,w) = P(m,t,u;v,w) for every real m,t,u,v,w. It includes equality of
coefficients outside the displayed support, where the coefficients are zero.

The 70 rows and all 350 coefficient strings are those of notes/endpoint-one-spectral-gap.md at
public revision 95d8d9a90d4ef0aa06be8ba5ce70d3355838385c. Their orientation is ascending powers
of v, homogenized as v^ell w^(4−ell). The actual native identity expands the explicit
determinant-bound A,B,D,N and the whole displayed sum. Textual row correspondence identifies
the public data; the full polynomial identity supplies its algebraic connection to F. Neither a
selected row nor a numerical anchor supplies that connection.

All displayed coefficients are positive. If m,t,u,v,w are nonnegative and v+w > 0, every term
of P is nonnegative. Its (0,0,0) row is already strictly positive: if w > 0 its 2654208w⁴ term
is positive, and if w = 0 then v > 0 and its 188596v⁴ term is positive. Thus P > 0 without
requiring positive parameter increments.

For sorted 8 ≤ a ≤ b ≤ c, set m = a−8, t = b−a, u = c−b, v = x and w = 4−x. All five variables
are nonnegative on the entire closed interval and v+w = 4 > 0. Direct homogeneous substitution
gives J(a,b,c;x,4−x) = 256F(x), so the table proves F(x) > 0 there. At x = 0 it uses the w⁴
coefficients; at x = 4 it uses the v⁴ coefficients. The strict values at both endpoints follow
directly, and x = 1 is covered by v = 1,w = 3. No limiting argument or division by 4−x is used
for this closed-interval proof.

The original rational form of the same complete identity is also retained: for every real m,t,u
and every z ≥ 0, (1+z)⁴F(8+m,8+m+t,8+m+t+u;4z/(1+z)) = P(m,t,u;z,1). Here F(a,b,c;x) means
evaluation of the explicit quartic at those parameters, and 1+z > 0. On 0 ≤ x < 4 the inverse z
= x/(4−x) recovers this form, with positive denominator. The homogeneous argument above
supplies x = 4 directly as well.

The scalar formula in s,p,r gives the exact symmetries F(a,b,c;x) = F(b,a,c;x) and F(a,b,c;x) =
F(a,c,b;x) for every real a,b,c,x. These two adjacent swaps cover all six weak ordering cases,
including ties. Sorting any original unsorted triple with each entry at least eight and
transporting the scalar value proves the same closed positivity for that original triple. This
uses scalar polynomial symmetry and makes no unproved matrix-permutation assertion.

Now add actual h_C(1) = 0 for that unsorted triple. Exact division gives χ_C(X) = X(X−1)F(X),
with F monic of degree four. Positive weights and the established similarity supply a split
real characteristic polynomial with one simple zero and five positive roots. Thus F also splits
over the reals and its root multiset has four entries, all positive. The complete quotient-root
multiset is {0,1}+F.roots. Strict F(x) > 0 on the closed interval excludes every residual root
there, so all four residual roots are strictly greater than four. In particular F(1) > 0 and
h_C′(1) = F(1) > 0; the quotient root one has algebraic multiplicity exactly one and is the
smallest positive root. High-root repetitions remain allowed. If those four roots happen to be
integers, each is at least five; this is a location restriction, not an obstruction to integral
splitting or a classification.

The following is the complete table used in the identity. Each row lists (i,j,k) followed by
(g₀,g₁,g₂,g₃,g₄); all other (i,j,k) coefficients are zero. This finite polynomial identity
proves a theorem on the entire unbounded real orthant. Off h_C(1) = 0, positivity still holds
but F.roots are not asserted to be quotient roots.

| i | j | k | (g₀,g₁,g₂,g₃,g₄), ascending v powers |
| --- | --- | --- | --- |
| 0 | 0 | 0 | [2654208,7797220,7836988,2882316,188596] |
| 0 | 0 | 1 | [651264,2000436,2147180,896892,98884] |
| 0 | 0 | 2 | [48640,158956,186612,90916,14620] |
| 0 | 0 | 3 | [1088,4028,5556,3380,764] |
| 0 | 1 | 0 | [1302528,4000872,4294360,1793784,197768] |
| 0 | 1 | 1 | [248320,796560,909936,423408,61712] |
| 0 | 1 | 2 | [13568,46408,57976,31000,5864] |
| 0 | 1 | 3 | [200,764,1092,692,164] |
| 0 | 2 | 0 | [248320,796560,909936,423408,61712] |
| 0 | 2 | 1 | [34176,115056,140592,72720,13008] |
| 0 | 2 | 2 | [1192,4328,5832,3448,752] |
| 0 | 2 | 3 | [8,32,48,32,8] |
| 0 | 3 | 0 | [22784,76704,93728,48480,8672] |
| 0 | 3 | 1 | [1984,7128,9480,5512,1176] |
| 0 | 3 | 2 | [32,128,192,128,32] |
| 0 | 4 | 0 | [992,3564,4740,2756,588] |
| 0 | 4 | 1 | [40,160,240,160,40] |
| 0 | 5 | 0 | [16,64,96,64,16] |
| 1 | 0 | 0 | [1953792,6001308,6441540,2690676,296652] |
| 1 | 0 | 1 | [399360,1275208,1446648,664984,94184] |
| 1 | 0 | 2 | [23872,80732,99284,51860,9436] |
| 1 | 0 | 3 | [400,1528,2184,1384,328] |
| 1 | 1 | 0 | [798720,2550416,2893296,1329968,188368] |
| 1 | 1 | 1 | [121792,404076,483620,242180,40844] |
| 1 | 1 | 2 | [4992,17580,22804,12836,2620] |
| 1 | 1 | 3 | [49,192,282,184,45] |
| 1 | 2 | 0 | [121792,404076,483620,242180,40844] |
| 1 | 2 | 1 | [12576,43572,55308,30204,5892] |
| 1 | 2 | 2 | [293,1088,1506,920,209] |
| 1 | 2 | 3 | [1,4,6,4,1] |
| 1 | 3 | 0 | [8384,29048,36872,20136,3928] |
| 1 | 3 | 1 | [488,1792,2448,1472,328] |
| 1 | 3 | 2 | [4,16,24,16,4] |
| 1 | 4 | 0 | [244,896,1224,736,164] |
| 1 | 4 | 1 | [5,20,30,20,5] |
| 1 | 5 | 0 | [2,8,12,8,2] |
| 2 | 0 | 0 | [599040,1912812,2169972,997476,141276] |
| 2 | 0 | 1 | [97920,323344,384336,190320,31408] |
| 2 | 0 | 2 | [4392,15288,19528,10760,2128] |
| 2 | 0 | 3 | [49,192,282,184,45] |
| 2 | 1 | 0 | [195840,646688,768672,380640,62816] |
| 2 | 1 | 1 | [22392,76464,95152,50480,9400] |
| 2 | 1 | 2 | [612,2208,2952,1728,372] |
| 2 | 1 | 3 | [3,12,18,12,3] |
| 2 | 2 | 0 | [22392,76464,95152,50480,9400] |
| 2 | 2 | 1 | [1542,5472,7164,4080,846] |
| 2 | 2 | 2 | [18,68,96,60,14] |
| 2 | 3 | 0 | [1028,3648,4776,2720,564] |
| 2 | 3 | 1 | [30,112,156,96,22] |
| 2 | 4 | 0 | [15,56,78,48,11] |
| 3 | 0 | 0 | [97920,323344,384336,190320,31408] |
| 3 | 0 | 1 | [12000,40784,50416,26480,4848] |
| 3 | 0 | 2 | [359,1280,1686,968,203] |
| 3 | 0 | 3 | [2,8,12,8,2] |
| 3 | 1 | 0 | [24000,81568,100832,52960,9696] |
| 3 | 1 | 1 | [1829,6400,8226,4568,913] |
| 3 | 1 | 2 | [25,92,126,76,17] |
| 3 | 2 | 0 | [1829,6400,8226,4568,913] |
| 3 | 2 | 1 | [63,228,306,180,39] |
| 3 | 3 | 0 | [42,152,204,120,26] |
| 4 | 0 | 0 | [9000,30588,37812,19860,3636] |
| 4 | 0 | 1 | [735,2560,3270,1800,355] |
| 4 | 0 | 2 | [11,40,54,32,7] |
| 4 | 1 | 0 | [1470,5120,6540,3600,710] |
| 4 | 1 | 1 | [56,200,264,152,32] |
| 4 | 2 | 0 | [56,200,264,152,32] |
| 5 | 0 | 0 | [441,1536,1962,1080,213] |
| 5 | 0 | 1 | [18,64,84,48,10] |
| 5 | 1 | 0 | [36,128,168,96,20] |
| 6 | 0 | 0 | [9,32,42,24,5] |

## The full equality-locus spectrum and its principal blocks

For every real 2 ≤ a ≤ b, put c = b(b+2)−a and s = a+b+c. Then c−b = b²+(b−a) > 0, so the
actual ordered global spectral theorem applies and its all-two exception is absent. In the
ascending characteristic-root multiset of the same quotient C, the full statement is 0 = λ₁ <
λ₂ < λ₃ = b < a+b < s < λ₄ ≤ λ₅ ≤ λ₆. The root b has algebraic multiplicity one. The following
argument uses the actual characteristic product and its strict sign.

Keep the residual-quartic A,B,D,N at these parameters. Put q₃ = b−A−1, q₂ = bq₃+A+B, q₁ =
bq₂−B−D, q₀ = acs(p+s), and Q₄(X) = X⁴+q₃X³+q₂X²+q₁X+q₀. The literal determinant gives h_C(X) =
(X−b)Q₄(X), even without h_C(1) = 0. With q = ac, its exact value at b is Q₄(b) = −b(b+1)L,
where L = (b−2)q²+b[(b−2)(b²+5b+8)+12]q+b³(b+1)(b+2)². The factorization and value identity
hold for all real a,b after c = b(b+2)−a; on 2 ≤ a ≤ b all terms of L are nonnegative and its
final term is positive. Hence Q₄(b) < 0.

The global application supplies h_C(X) = ∏ᵢ₌₂⁶(X−λᵢ), λ₂ ≤ λ₃ < a+b and s < λ₄ ≤ λ₅ ≤ λ₆. Since
(X−b) divides h_C, b equals an actual positive root; b < s excludes the high three. If λ₂ = b,
cancellation of one monic factor would give Q₄(X) = ∏ᵢ₌₃⁶(X−λᵢ). All four factors at b would be
nonpositive, so Q₄(b) ≥ 0, contradicting its strict sign. Therefore λ₃ = b and λ₂ < b. Together
with simple zero, positivity and the high gap this proves the full six-root order and exactly
one occurrence of b. Equivalently χ_C(X) = X(X−λ₂)(X−b)P₃(X), where P₃(X) = ∏ᵢ₌₄⁶(X−λᵢ) is
monic of degree three and has exactly those high roots with multiplicity.

Every proper principal block of the symmetric representative S is positive definite. To see
this for any injective coordinate selector omitting a coordinate j, extend a nonzero block
vector by zero on omitted coordinates. If its nonnegative quadratic form vanished,
Matrix.PosSemidef.dotProduct_mulVec_zero_iff would put the extension in ker(S). Transport by
the proved positive diagonal and permutation puts it in the constant kernel of C. The zero at j
forces that constant to vanish, contradicting the nonzero vector. This proves the assertion for
every proper principal block, including all choices of deleted supports, rather than just the
two blocks displayed next.

Delete singleton support 2, which is stored index 1 in S. Order the retained supports as
13,1,3,12,23, with stored selector [4,0,2,5,3]. Its principal block B_del is [b] direct-sum T.
The four-by-four T has original support order 1,3,12,23 and stored selector [0,2,5,3]. Put ρ =
sqrt(a)sqrt(b)sqrt(c) > 0 and η = sqrt(a)sqrt(c). Its literal matrix is T =
[[b+c+bc,−η,0,−ρ],[−η,a+b+ab,−ρ,0],[0,−ρ,c,0],[−ρ,0,0,a]]. These square-root products use the
existing rootWeights, so η = sqrt(ac) and ρ = sqrt(abc) on this domain.

In the bordered order 2;13,1,3,12,23, the full S is [[a+c+ac,zᵀ],[z,B_del]] with the complete
coupling vector z = (−ρ,−sqrt(a)sqrt(b),−sqrt(b)sqrt(c),0,0)ᵀ. In particular the coupling to
the isolated support 13 is −ρ ≠ 0.

Exact determinant expansion gives charpoly(T) = (X−b)K(X) and charpoly(B_del) = (X−b)²K(X),
where K(X) = X³−b(b²+4b+5)X²+[ac(b²+1)+b²(b+2)(b²+3b+3)]X−abc(b+3). At zero these identities
also give det(T) = ab²c(b+3) > 0 and det(B_del) = ab³c(b+3) > 0. The cubic value has the exact
positive decomposition K(b) = b(b+1)[a(b−a)(b−2)+ab(b−2)(b+1)+b²(b+1)(b+2)] > 0, including b =
2 and repeated parameters.

Because T is positive definite and symmetric, all its characteristic roots are real and
positive. Its factorization therefore makes K a split monic cubic of degree three with positive
roots κ₁ ≤ κ₂ ≤ κ₃, counted with multiplicity. Coefficient comparison gives κ₁+κ₂+κ₃ =
b(b²+4b+5) > 3b, hence κ₃ > b. The product K(b) = (b−κ₁)(b−κ₂)(b−κ₃) > 0 excludes equality with
b and forces κ₁ < b < κ₂: if κ₁ ≥ b the three factors are nonpositive, and if κ₂ ≤ b the first
two are nonnegative and the last is negative; either case would make the product nonpositive.
Thus 0 < κ₁ < b < κ₂ ≤ κ₃.

The complete cubic root multiset is {κ₁,κ₂,κ₃}; the complete T multiset is {κ₁,b,κ₂,κ₃}; and
the complete deleted-block multiset is {κ₁,b,b,κ₂,κ₃}. Consequently K has no occurrence of b, T
has exactly one and B_del exactly two, whereas the full quotient has exactly one as proved
above. Equality between κ₂ and κ₃, or between full high roots, remains allowed.

Finally assume actual h_C(1) = 0 on this same locus. Since b ≥ 2, the root one can occupy only
λ₂; every other positive position is at least b. Thus λ₂ = 1 and is simple. Exact polynomial
division yields χ_C(X) = X(X−1)(X−b)P₃(X) and F(X) = (X−b)P₃(X). The monic cubic P₃ has exactly
the actual multiset {λ₄,λ₅,λ₆}, each strictly greater than s. This endpoint assertion does not
require a ≥ 4 or a ≥ 8. It is distinct from the earlier endpoint-comparison equality family b =
a,c = (a−1)(2a−1).

The equality-locus statement and displayed block/cubic mathematics are attributed to the
proposition in paper/sections/endpoint-one-spectrum.tex, lines 209–260, at
b93becea662a746badeadba42fdc3d3eb3db9382. The exposition follows the completed actual
spectral-product/sign and cubic-trace applications.

### Direct public sources for the residual applications

- [The endpoint-one coefficient-window corollary](https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/sections/endpoint-one-spectrum.tex#L121) gives the source E1 statement.
- [The total-sum coefficient note](https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/4a451ac51055c6d04926967749196f12ac8e49c8/notes/total-sum-spectral-gap.md) supplies its related real coefficient-window discussion.
- [The complete closed-interval residual note](https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/95d8d9a90d4ef0aa06be8ba5ce70d3355838385c/notes/endpoint-one-spectral-gap.md) supplies all 70 table rows and 350 entries; the pinned ordinary note has SHA256 `4d7c174bdfc92e139a5397c8a231ff175e540a1013bfadba80421e8ca6d0c1eb`.
- [The equality-locus spectral proposition](https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/sections/endpoint-one-spectrum.tex#L209) supplies the source E4 statement and block/cubic formulas. The complete paper section retains SHA256 `16c52326f7c88bf538ee2b70bfc4f6c6e4b6901f93d963cd288ab96e4d4c50f5`.

## Evidence scope and the remaining geometric frontier

The source-bound transient packet supplies the full actual E1, E2 and E4 applications described
here, with exact typed targets, actual-carrier correspondence, complete coefficient-table
identity, source/object/receipt bindings and recorded dependencies. Its completed execution is
author-reported and its ordinary custody was independently verified. The independent entire-native
review 36807 is complete with three approve verdicts, covering the first actual transient E1/E2/E4
application batch and its recorded domains, clauses, source/type/dependency/axiom and custody
evidence. That review does not complete whole-source review or canonical delivery. The corrected-source review 33465 on 3 November 2026 supported the mathematical, proof-correspondence and conservation scope but returned FIX (architecture approve; quality and tests reject) for stale current clause-map evidence status. This canonical integration corrects that finite presentation defect; independent review of the entire final published unit remains required. This candidate performs no new formal execution and admits none of
those transient application names as repository Lean, Reg or Describe declarations. The
existing Describe statements retain their exact displayed scope.

The accepted all-integer finiteness result PR25647, F1–F3/G1–G5 application PR25764 and H1–H5
PR25845 remain preserved. The sections “Exact actual matrix and characteristic-polynomial correspondence”
and “Exact quartic algebra over characteristic-zero fields” retain all delivered E3 substance. Full E3 still requires actual smooth proper models, full constants,
finite separable model maps, finite and infinity local DVRs with uniformizers, valuations and
different, genus three and ten, both Riemann–Hurwitz applications, exhaustive second-cover
parity and the geometric integer/Siegel interface. The separate first finite-local native implementation 16364 completed on 3 November 2026
and its exact source and evidence were preserved; its initial independent implementation
review, canonical admission and publication remain pending. None of that temporary
local-geometry source is added by this exposition. Algebraic nonsquares, gcds, field degrees and the already proved elementary
integer finiteness do not discharge those model-level obligations.

This application exposition conserves the separately published E3 matrix and quartic-algebra
source together with the receiving dev content. Canonical generation, readable-output
inspection and applicable gate evidence are separate from prior native acceptance and are
bound to the published source revision. The entire final canonical independent review, all
applicable final-head CI, guarded merge and first-dev verification remain distinct integration
obligations until actually completed. Actual formal and canonical execution belongs to the
Mac Studio authenticated NyxID HECA service selected by the user. The complete original 21
tasks and issues 17673–17677 remain unchanged; neither full E3 nor whole-goal completion
follows from this E1/E2/E4 exposition.

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
