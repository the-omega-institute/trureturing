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
  - D5/S3/Quantum/Matrix/WeightedTraceGram
  - D5/S3/Quantum/Matrix/HsfContractionGrams
  - D5/S3/Quantum/Matrix/HsfContractionCubic
  - D5/S3/Quantum/Matrix/HsfIdentityCubicCompatibility
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

The current formal library extends this record with a separate, explicitly
scoped two-level supplier. `D5/S3/Quantum/Matrix/RpowPencilTaylor` proves
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
That two-level supplier does not provide a three-level or arbitrary-spectrum
denominator theorem. These results do not claim the full all-`alpha` HSF conjecture, a novelty
result, or an official open-problem resolution. The primary HSF source and
the original radial `alpha=3` exposition above remain the citation anchor.

## Cubic identity denominator in arbitrary finite dimension

`HsfIdentityCubicCompatibility.identity_cubic_compatibility` treats the actual
CFC curve

\[
f(t)=\operatorname{Re}\operatorname{Tr}\left[
 ((I+tK)^{-1/3}(U+tH)(I+tK)^{-1/3})^3\right].
\]

For every finite complex matrix size, Hermitian \(K\), and PSD endpoints
\(U+H,U-H,I+K,I-K\), it gives \(f''(0)\ge0\) and
\(|f'''(0)|\le5f''(0)\). In particular, this covers every positive
definite \(U\) and Hermitian \(H,K\), without commutativity assumptions.
Singular endpoints and zero Hessian are included. The actual derivative
supplier is `HsfIdentityCubicDerivatives.identity_cubic_trace_derivatives`;
no Taylor-coefficient premise is assumed.

The positive-direction certificate sets \(A=H,B=U-H\),
\(Q=A-(A+B)K\), \(C_A=AK-KA\), and \(C_B=BK-KB\).
`HsfContractionCubic.coefficient_gap_identity` uses the ordered basis
\(Q,QK,C_A,C_AK,KC_A,C_B,C_BK,KC_B\) and the exact trace order
\(\operatorname{Re}\operatorname{Tr}(Lq_i^*Rq_j)\).
Its four localizers have weights \((A,I-K),(A,K),(B,I-K),(B,K)\).
`HsfContractionGrams.grams_posSemidef` supplies the fixed eight by eight
integer PSD matrices by exact rational LDL reconstruction, including the
zero first row and column of \(M_{00}\).
`WeightedTraceGram.weighted_traceGram_nonneg` supplies positivity in
independent arbitrary finite physical and coefficient dimensions.
Only cyclic trace rotations are used, with neither reversal equivalence
nor \(K^2=K\). The exact residual has 52 surviving cyclic classes.
The signed transfer theorem identifies the actual derivatives as
\(f''=4g_+''\) and \(f'''=12g_+''+8g_+'''\), where
\(H_+=(U+H)/2,K_+=(I+K)/2\). The scalar feasible direction
\(U=H=I,K=-I\) attains \(f''(0)=24,f'''(0)=120\), so five is sharp.
The certificate is repository-derived from the supplied integer matrices;
no bibliographic-priority claim is made.

There is also a commuting-denominator application. For positive definite
\(X,Y\), Hermitian \(H,K\), PSD \(X\pm H,Y\pm K\), and
\(YK=KY\), set
\[
\widehat X=Y^{-1/3}XY^{-1/3},\quad
\widehat H=Y^{-1/3}HY^{-1/3},\quad
\widehat K=Y^{-1/2}KY^{-1/2}=Y^{-1}K.
\]
Congruence transfers the four endpoints. Commuting functional calculus gives
\((Y+tK)^{-1/3}=Y^{-1/3}(I+t\widehat K)^{-1/3}\) near zero, so the
original alpha-three path equals the normalized identity-denominator path.
Neither \(X\) nor \(H\) needs to commute with \(Y\) or \(K\).
This application is explained in the owning derivative Scribe; the commuting
factorization and endpoint transport are mathematical exposition, not extra
Lean declarations. Full general noncommuting \(Y,K\) remains **OPEN**:
a congruence or first-jet match does not supply the actual second and third
jets needed by this certificate.

The new source-selection audit bindings remain unfinished under
https://github.com/the-omega-institute/trureturing/issues/23332;
typed audit attempts are not `declared_validated` evidence.

## Verified locators

- arXiv:2502.05627v1, Conjecture 6.2 and the preceding scalar discussion.
- DOI 10.1007/s10107-025-02314-0, Proposition 3 and Conjecture 1.
- arXiv:2310.03227v1, Theorem 1.4 and its power identity, Lemma 1.6, and Proposition 3.8(1).

These sources identify the target, scalar predecessor, and analytic radial
measure implication. This note does not establish bibliographic priority or
exclude a later resolution.
