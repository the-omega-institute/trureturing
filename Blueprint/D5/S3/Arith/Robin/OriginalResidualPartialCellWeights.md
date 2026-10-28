# The Original Partial-Cell Projection

## Abstract

The exact real partial cells define an affine Gram projection with two zero moments and explicit mass and complete zero-extension variation bounds.

Let N be a natural number at least 3, with real N<a<b<2N. Write lambda(t)=1/(t log(t)), k(t)=(log(t)+1)/(t^2 log(t)^2), and S={N,...,2N-1}. Block sums below use this same S. The integral retains the literal real endpoints and all partial cells. Coefficients c0 and c1 are real and have no sign restriction.

**Definition 1.1 (Exact intersection mass).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.omega`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.omega` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a,b and natural m, omega(a,b,m) is the Lebesgue integral of k(t) over [a,b] intersect [m,m+1]. Empty and singleton intersections have zero mass.

**Definition 1.2 (Discrete weight).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.w`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.w` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural m, w(m)=1/[m(m+1)], using real division.

**Definition 1.3 (Affine sample).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.v`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.v` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural N,m, v(N,m) is the real two-vector (1,m/N).

**Definition 1.4 (Actual finite Gram).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.gram`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.gram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural N and i,j in Fin 2, G(N)[i,j]=sum_(m in S) w(m)v(N,m)[i]v(N,m)[j].

**Definition 1.5 (Original cell datum and terminal value).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.datum`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.datum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural N,m and real a,b, d(N,a,b,m)=log(N)omega(a,b,m)/w(m) when m is different from 2N, and d(N,a,b,2N)=0.

**Definition 1.6 (Actual normal-equation right side).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.rhs`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.rhs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural N, real a,b and i in Fin 2, h(N,a,b)[i]=sum_(m in S) w(m)d(N,a,b,m)v(N,m)[i].

**Definition 1.7 (Gram determinant).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.delta`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural N, Delta(N)=G(N)[0,0]G(N)[1,1]-G(N)[0,1]^2.

**Definition 1.8 (Actual Cramer coefficients).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.c`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.c` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural N and real a,b, c0=(G11*h0-G01*h1)/Delta and c1=(G00*h1-G01*h0)/Delta, with all entries taken at those same N,a,b.

**Definition 1.9 (Affine residual with a separate terminal value).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.residual`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.residual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural N,m and real a,b, r(N,a,b,m)=d(N,a,b,m)-c0-c1*m/N when m is different from 2N. Its value at 2N is separately zero.

**Definition 1.10 (Zero-extended projected coefficient).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.coeff`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.coeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural N,m and real a,b, A(N,a,b,m)=w(m)r(N,a,b,m) for N<=m<2N, and is zero elsewhere.

**Definition 1.11 (Absolute coefficient mass).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.mass`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural N and f from the naturals to the reals, mass(N,f)=sum_(m in S)|f(m)|.

**Definition 1.12 (Both boundary jumps).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.variation`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.variation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural N and f from the naturals to the reals, variation(N,f)=|f(N)|+sum_(N<=m<2N-1)|f(m+1)-f(m)|+|f(2N-1)|. For N>=1, this is the complete variation of the finite sequence extended by zero.

**Definition 1.13 (Exact harmonic factor).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.harmonic`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.harmonic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural N, J(N)=sum_(m in S)1/(m+1), equivalently sum_(N<j<=2N)1/j.

**Theorem 1.14 (Exact projection, two moments, mass and variation).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.or6_partialCell_variation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.or6_partialCell_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N>=3 and real N<a<b<2N, put ell_m=max(a,m), u_m=min(b,m+1). For every natural m, omega_m=lambda(ell_m)-lambda(u_m) if ell_m<u_m, and omega_m=0 otherwise. The actual Delta(N) is strictly positive, c=G^(-1)h, and Gc=h. The actual coefficients satisfy sum_(m in S) A_m=0 and sum_(m in S)m*A_m=0. The three terminal values d(2N), r(2N) and A(2N) are zero.

Write L=log(N), V=variation(N,A), and M=mass(N,A). Then V<=2L*k(a)+2(|c0|+|c1|)/[N(N+1)] <=2L*k(N)+2(|c0|+|c1|)/[N(N+1)], and M<=L[lambda(a)-lambda(b)]+|c0|/(2N)+|c1|J(N)/N.

The normal equations follow from the positive actual finite Gram: a nonzero affine polynomial cannot vanish at both samples N and N+1. The cell integral is evaluated with the existing reciprocal-logarithm density-integral theorem. For the variation estimate, the truncated density is the difference of two decreasing functions, a capped density and its constant left step. Averaging over a unit cell preserves their decrease. The finite difference sum telescopes with both endpoint jumps and is at most 2k(a). Both decreasing discrete sequences w(m) and (m/N)w(m) have complete variation 2/[N(N+1)]. Their masses are 1/(2N) and J(N)/N. Triangle inequalities apply to the same signed coefficients.

This is a finite coefficient construction. It supplies the two moments and explicit absolute bounds for the unchanged residual. It does not establish a signed residual estimate, compensation of the affine observations, analytic spectral suppliers, the original infinite construction, strict Robin for all integers above 5040, or the Riemann hypothesis.

**Theorem 1.15 (Actual density supplies the original coefficient energy).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.or6_partialCell_energy_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.or6_partialCell_energy_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N>=3 and real a,b with N<=a<=b, use the same literal partial-cell masses, full-block Gram and original coefficients A_m. Then sum_(N<=m<2N) A_m^2/w(m) <= (1+1/log(N))^2/(8*N). The coefficient A already contains the factor log(N). Equal endpoints are included. The endpoint b needs no upper bound: every original cell integral is clipped to its own unit cell.

Write B=1+1/log(N). On each original unit cell, k(t)=[1/log(t)+1/log(t)^2]/t^2 is bounded by [1/log(N)+1/log(N)^2]/t^2. The exact integral of 1/t^2 over [m,m+1] is w(m). Positivity of the clipped density therefore gives 0<=d_m<=B for the original datum d_m=log(N)*omega_m/w(m). The two exact moments eliminate the cross terms in the weighted least-squares expansion about the constant B/2. Hence the residual energy is at most sum w(m)*(d_m-B/2)^2, which is at most B^2/4 times the weight mass sum w(m)=1/(2*N), giving B^2/(8*N). Both original Cramer coordinates and their mixed correction remain in that expansion.

This supplies a finite upper bound from the actual density rather than assuming an energy allowance. It does not prove a sharp finite endpoint maximizer, a signed residual estimate, an analytic Mobius-prefix rate, the complete cutoff payments, strict Robin above 5040 or RH.

**Theorem 1.16 (Exact public interface to the unchanged original projection).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.response_projection_interface`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.response_projection_interface` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N>=3, on S(N)={m in N:N<=m<2N}, the exact original Gram entries satisfy G00=sum w(m), G01=sum w(m)*m/N, G10=G01, and G11=sum w(m)*(m/N)^2; the original determinant Delta(N)>0. For every real a,b, sum A(N,a,b,m)=0 and sum m*A(N,a,b,m)=0. For every real a,b and every natural m in S(N), A(N,a,b,m)=log(N)*omega(a,b,m)-c0*w(m)-c1*[w(m)*m/N]. There are no endpoint order, strictness or upper-bound hypotheses on a,b in this interface.

This single additive theorem binds the original private Gram-entry, positive-determinant, exact-moment and on-block coefficient proofs directly. The separate response-adjoint module is its actual consumer. No original definition, proof, accepted energy content or owner import is replaced. It makes no interval-sign, cofinal or RH assertion. This interface and its Reg/Scribe additions have completed local scoped validation; repository PR and CI acceptance remain separate delivery steps.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.c`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.coeff`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.datum`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.delta`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.gram`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.harmonic`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.mass`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.omega`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.or6_partialCell_energy_bound`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.or6_partialCell_variation`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.residual`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.response_projection_interface`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.rhs`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.v`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.variation`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.w`
- Dependency: [D5/S3/Arith/Robin/ActualRobinClockCovariance](ActualRobinClockCovariance.md)
- Dependency: [D5/S3/Arith/Robin/MellinWeightedVariation](MellinWeightedVariation.md)
