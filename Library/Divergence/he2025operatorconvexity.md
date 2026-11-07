---
bibkey: he2025operatorconvexity
authors: Kerry He, James Saunderson, and Hamza Fawzi
year: 2025
title: Operator convexity along lines, self-concordance, and sandwiched Rényi entropies
doi: 10.1007/s10107-025-02314-0
url: https://arxiv.org/abs/2502.05627v1
claim: Conjecture 6.2 in arXiv v1, renumbered Conjecture 1 in the journal article, proposes the sharp compatibility parameter (2 alpha - 1)/3 for the sandwiched trace function in every finite dimension.
strata_touched:
  - D5/S3/Quantum/Matrix/HsfCubicRadial
  - D5/S3/Quantum/Matrix/RpowPencilTaylor
  - D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate
  - D5/S3/Quantum/Matrix/HsfBalancedCfcBridge
  - D5/S3/Quantum/Matrix/HsfLocalSpectrumTrace
  - D5/S3/Quantum/Matrix/HsfLocalSpectrumSupplier
  - D5/S3/Quantum/Matrix/HsfThreeLevelSupplier
license: citation-only
triage: anchor
---

# Sandwiched trace compatibility

For positive definite complex Hermitian matrices, the source considers

\[
\Psi_\alpha(X,Y)
=\operatorname{Tr}\!\left[
  \left(Y^{(1-\alpha)/(2\alpha)}X
        Y^{(1-\alpha)/(2\alpha)}\right)^\alpha
\right].
\]

The conjecture covers every positive integer dimension and every
\(\alpha\ge2\). In directional derivative form, for Hermitian directions
with \(X\pm H,Y\pm K\succeq0\), its proposed sharp estimate is
\(|g'''(0)|\le(2\alpha-1)g''(0)\), where
\(g(t)=\Psi_\alpha(X+tH,Y+tK)\).
The journal article's Proposition 3 proves the scalar result and its
sharpness; Conjecture 1 asks for the matrix extension.

The repository's `HsfCubicRadial` proves the normalized polynomial-trace
estimate at \(\alpha=3\): for Hermitian \(A,B\) with
\(A\pm B\succeq0\), the actual function
\(f(t)=\operatorname{Re}\operatorname{Tr}[(A+tB)^3]/(1+kt)^2\)
satisfies \(f''(0)\ge0\) and
\(|f'''(0)|\le(1+4|k|)f''(0)\). Over \(|k|\le1\), the least
uniform constant is 5. Its proof is repository-derived and allows
noncommuting matrices. Its physical radial application takes
\(K=kY\), \(S=Y^{-1/3}\), \(A=SXS\), and \(B=SHS\).
For positive definite \(X,Y\) and Hermitian \(H\) with
\(X\pm H\succeq0\), positive-scalar CFC scaling identifies the original
trace function with \(f\) near zero. Thus its actual second and third
derivatives satisfy the same bound, including singular endpoints.
General second-variable directions remain outside this radial application;
other exponents are outside the existing FORMAL module scope, although the
analytic radial extension below covers every real \(\alpha\ge2\).

## Analytic radial extension (external measure theorem; not formalized)

Let \(X,Y>0\) be finite-dimensional complex Hermitian matrices,
\(\alpha\ge2\) be real, \(H=H^*\) with \(X\pm H\succeq0\),
and \(K=kY\) with \(|k|\le1\)
\(\bigl(Y\pm K\succeq0\bigr)\), and put
\(s=(1-\alpha)/(2\alpha)\),
\(A=Y^sXY^s\), and \(B=Y^sHY^s\). Then \(A>0\),
\(A\pm B\succeq0\), and for \(|t|<1\)
\[
g(t)=(1+kt)^{1-\alpha}\operatorname{Tr}(A+tB)^\alpha.
\]
Heinävaara, *Tracial Joint Spectral Measures*, arXiv:2310.03227v1,
Theorem 1.4 and the power identity following it, supplies a positive
measure \(\mu_{A,B}\) with
\(\operatorname{Tr}(A+tB)^\alpha
=\alpha(\alpha+1)\int|a+tb|^\alpha\,d\mu_{A,B}(a,b)\).
Lemma 1.6 gives half-plane support for a positive first coordinate, and
Proposition 3.8(1) gives the basis-change pushforward. Applying these to
\(A\), \(A+B\), and \(A-B\) yields the support containment
\(a\ge|b|\) \(\mu_{A,B}\)-almost everywhere. This is containment; no literal
equality with the whole cone is claimed.

For each \(\alpha\), push this measure forward with the weight \(a^\alpha\):
\[
\nu_\alpha(E)=\alpha(\alpha+1)\int_{a>0}a^\alpha
  1_E(b/a)\,d\mu_{A,B}(a,b),\qquad
\nu_\alpha([-1,1])=\operatorname{Tr}A^\alpha.
\]
The measure is finite because its mass is \(\operatorname{Tr}A^\alpha\);
no unweighted finiteness of \(\mu_{A,B}\) is assumed. The resulting
\(\nu_\alpha\) is alpha-indexed; no single measure for different exponents
is asserted. Therefore
\[
g(t)=\int_{[-1,1]}(1+tu)^\alpha(1+kt)^{1-\alpha}\,d\nu_\alpha(u).
\]
On every compact subinterval of \((-1,1)\), the integrand and its first
three derivatives are uniformly bounded (also for noninteger \(\alpha\) and
\(\alpha=2\)); dominated differentiation gives \(g\in C^3((-1,1))\).
Writing \(q_u(t)=(1+tu)^\alpha(1+kt)^{1-\alpha}\), scalar differentiation gives
\[
q_u''(0)=\alpha(\alpha-1)(u-k)^2,\qquad
q_u'''(0)=q_u''(0)\bigl[(\alpha-2)u-(\alpha+1)k\bigr].
\]
Consequently, including singular endpoints and zero Hessian,
\[
g''(0)\ge0,\qquad
|g'''(0)|\le[(\alpha-2)+(\alpha+1)|k|]g''(0)
\le(2\alpha-1)g''(0).
\]
If \(g''(0)=0\), positivity of the integral forces \(u=k\)
\(\nu_\alpha\)-almost everywhere, hence \(g'''(0)=0\). This is an
analytic consequence of the external measure theorem. The measure
prerequisite and this all-alpha corollary have no Lean proof here; arbitrary
independent \(H,K\) and the full HSF conjecture remain OPEN.

The formal library supplies the following actual-CFC results with explicit
spectral and directional scope. `D5/S3/Quantum/Matrix/RpowPencilTaylor` proves
for an arbitrary finite-dimensional positive definite complex Hermitian center
`Y` and Hermitian direction `K` that the actual CFC cube-root pencil is smooth
near zero (`contDiffAt_cubeRoot`), that its first three
factorial-normalized jets satisfy the ordered noncommutative cubic recurrences
(`cubeRoot_jet_recurrences`), and that the actual two-thirds power is smooth
(`contDiffAt_twoThirds`) with the corresponding ordered jet formula
(`normalized_twoThirds_jet`). Its fixed spectral-coordinate interface
(`cubeRoot_jet_spectral`) has strictly positive entrywise divisors, including
repeated eigenvalues; it does not assume commutation, a spectral floor, or a
derivative premise.

`D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate` supplies the finite
weighted PSD Gram certificate for the displayed two-level frame. The two
diagonal blocks may have arbitrary finite multiplicities and the off-diagonal
block is an arbitrary rectangular complex matrix, subject to positivity of the
full block direction. The diagonal blocks are therefore consequences of this
single full-block PSD hypothesis, not independent arbitrary-PSD inputs.
Singular directions and `r=1` are included, and the certificate keeps all
matrix multiplication orders. Its `supplier_of_cubic_recurrence` theorem is
the repository's balanced cubic algebraic certificate, not a claim about an
arbitrary spectrum.

`D5/S3/Quantum/Matrix/HsfBalancedCfcBridge.actual_twoLevel_supplier` consumes
the actual CFC jets and gives the stated weighted inequality in that supplied
two-level frame. Its
`D5/S3/Quantum/Matrix/HsfBalancedCfcBridge.transported_twoLevel_supplier`
version permits only the supplied finite reindexing, unitary conjugation, and
common positive scaling of the center and direction. It does not extract a
frame from a bare eigenvalue-count premise and does not provide nonunitary
congruence or arbitrary PSD diagonal blocks outside the displayed hypothesis.
The separate `HsfLocalSpectrumSupplier.finite_spectrum_local_supplier` gives
an explicit local all-`Z` theorem for every finite positive diagonal spectrum
`P=diag(p_i)` with at least two distinct levels. Set
\(\tau_{ij}=3\sqrt{p_ip_j}(p_i+p_j)/(2(p_i^2+p_ip_j+p_j^2))\) and
\(\delta=\min_{p_i\ne p_j}(1-\tau_{ij}^2)>0\).
For complex Hermitian `H` satisfying `H_ij=0` whenever `p_i=p_j`, let
\(r=\|H\|_F\le3\delta/32\) and `S=I+H`. For the actual factorial
derivatives `B_j` at zero of
\(P^{-1}(P^3+tP^{3/2}SP^{3/2})^{2/3}P^{-1}\), it proves, for every
Hermitian `Z`,
\[
\operatorname{Re}\operatorname{Tr}
 (B_3+2ZB_2+B_1Z^2-\tfrac5{48}B_1^3)\ge\delta r^2/6.
\]
Repeated spectral levels, arbitrary multiplicities, complex phases and `H=0`
are included. `HsfLocalSpectrumTrace.actual_trace_normalization` supplies the
general actual-CFC quadratic and cubic trace identities used in this proof.
The positive gap requires the stated equal-level block support restriction;
the result is local on this affine slice, with no global neighborhood or
arbitrary-direction claim. It does not claim the full all-`alpha` HSF
conjecture, novelty, or an official open-problem resolution. The primary HSF
source and the original radial `alpha=3` exposition remain the citation anchor.

## Uniform local supplier and global three-level supplier

`HsfLocalSpectrumSupplier.finite_spectrum_uniform_local_supplier` uses the
same actual function and factorial-normalized jets, with `S=I+H`, for every
finite positive diagonal spectrum. For arbitrary complex Hermitian `H,Z`,
put \(A_{ij}=\tau_{ij}H_{ij}\) and
\(g=\|H\|_F^2-\|A\|_F^2\). If \(\|H\|_F\le1/20\), then
\[
\operatorname{Re}\operatorname{Tr}
 (B_3+2ZB_2+B_1Z^2-\tfrac5{48}B_1^3)\ge g/6\ge0.
\]
The radius is independent of the spectrum and dimension. Equal-level blocks
of `H`, scalar spectra, repeated levels and the empty dimension are included;
there is no bound on `Z` or cross-level support restriction. This is a local
neighborhood result, rather than an arbitrary-spectrum global supplier.

`HsfThreeLevelSupplier.actual_threeLevel_supplier` proves the global
supplier in a supplied diagonal spectral frame: let `n` be any finite index
type, `level : n -> Fin 3`, and `p : Fin 3 -> R` have strictly positive
values, and put \(P=\operatorname{diag}(p_{\mathrm{level}(i)})\).
For every complex PSD `S`, define
\[
 F(t)=P^{-1}(P^3+tP^{3/2}SP^{3/2})^{2/3}P^{-1},\qquad
 B_j=(j!)^{-1}F^{(j)}(0).
\]
For every Hermitian `Z`, the same real trace expression is nonnegative,
without a smallness condition on `S`. The powers and jets are the actual CFC
ones. Label collisions, empty label fibres, arbitrary finite multiplicities,
complex phases, singular PSD `S` and the empty carrier are included.
The theorem takes this frame as data; it does not extract or transport one
from a bare eigenvalue-count premise.

For positive definite `S`,
`HsfThreeLevelSupplier.actual_threeLevel_PD_sylvester` also constructs the
Hermitian Sylvester solution and proves an exact equality criterion. Write
\(a_i=p_{\mathrm{level}(i)}\), let `c` denote
`HsfLocalSpectrumSupplier.spectralKernel`, and set
\[
 X_{ij}=\tau(a_i,a_j)S_{ij},\qquad
 Q_{ij}=\sum_k\left[\tfrac23\tau(a_i,a_k)\tau(a_k,a_j)
                  +3c(a_i,a_j,a_k)\right]S_{ik}S_{kj},\qquad D=Q-X^2.
\]
It proves `X` positive definite and supplies Hermitian `Y` with
\(XY+YX=D\). For this solution,
\[
 E=4\operatorname{Re}\operatorname{Tr}(S^3-X^3)
   -6\operatorname{Re}\operatorname{Tr}(XD)
   -6\operatorname{Re}\operatorname{Tr}(DY)\ge0,\qquad
 E=0\ \Longleftrightarrow\ PS=SP.
\]
This rigidity statement requires positive definite `S`; it asserts no
singular-PSD rigidity. These results give no global supplier for arbitrary
spectra, all-exponent theorem, full HSF resolution or novelty claim.

The corresponding source-binding registrations remain `declared_unresolved`:
source-selection reconstruction and `escapeFrom` evidence are missing under
[issue 23103](https://github.com/the-omega-institute/trureturing/issues/23103)
(`IE-C050`, `source.selection_missing`). Kernel acceptance does not validate
those audits.

## Probability transform derivative bounds

`D5/S3/Analytic/Probability/ResolventPowerThirdOrder` proves a separate
scalar analytic ingredient. For an arbitrary probability measure, a measurable
real random variable `R` in `[0,1]` almost everywhere, and
`K(s) = integral (1 + R*s)^(-1)`, define
`G(s) = (1 + a*s)^(q+1) * K(s)^q` using real powers.
`powerCurve_derivatives` identifies the actual second and third iterated
derivatives at zero with their first-three-moment formulas, for every real
`a` and `q`. `powerCurve_third_order` proves, for `a` in `[0,1]` and `q>0`,
that `G''(0)>=0`, that `G'''(0)<=(q-1)*G''(0)` when `q>=1`, and that
`G'''(0)<=0` when `q<=1`.

The proof differentiates the actual integral under a uniform kernel bound,
then uses variance bounds and integrals of nonnegative weighted squares.
It assumes neither differentiability nor finite support; singular laws,
endpoint atoms and zero curvature are included. A Dirac law at zero with
`a=1` attains the supercritical coefficient `q-1`.
These are formal probability bounds. The Stieltjes representation of the
actual noncommuting matrix pencil, its rank-one matrix transfer, and the
full HSF conjecture remain separate unproved obligations here. No literature
priority or open-problem resolution is claimed for this module.

## Verified locators

- arXiv:2502.05627v1, Conjecture 6.2 and the preceding scalar discussion.
- DOI 10.1007/s10107-025-02314-0, Proposition 3 and Conjecture 1.
- arXiv:2310.03227v1, Theorem 1.4 and its power identity, Lemma 1.6, and Proposition 3.8(1).

These sources identify the target, scalar predecessor, and analytic radial
measure implication. This note does not establish bibliographic priority or
exclude a later resolution.
