# Actual K1 and L4 spectral purity

## Abstract

Continuous literal-K1 and top-six/bottom-ten purity bound with natural rounding.

**Theorem 1.1 (Rounded purity for every dimension at least 56).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ContinuousSpectrumAssembly.actual_k1_l4_purity_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ContinuousSpectrumAssembly.actual_k1_l4_purity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N>=56 and arbitrary real l:Fin N to Real, assume l is antitone, each l_i>=0, sum l_i=1, and sum over i:Fin 6 of l_i is at most sum over i:Fin 10 of l_(N-10+i). Indices are zero based and every displayed index is interpreted in Fin N. The remaining premise is positive semidefiniteness of the literal symmetric K1 matrix with rows [2 l_(N-1),l_(N-2)-l_0,l_(N-4)-l_1], [l_(N-2)-l_0,2 l_(N-3),l_(N-5)-l_2], [l_(N-4)-l_1,l_(N-5)-l_2,2 l_(N-6)]. Then sum l_i^2<=target(N), where target(N)=(9 Real.ofNat(N)+16 Real.ofNat(t))/(3 Real.ofNat(N)+2 Real.ofNat(t))^2 and t is the natural quotient (3*N+4)/8. Natural division precedes coercion to Real. These are the complete parameters and premises; zero entries, repeated entries and singular PSD matrices are allowed.

The literal quadratic forms at (1,1,1) and (1,1,0) give respectively sum of the first three entries<=sum of the last six and l_0<=sum of the last three. For N>=67 the existing three_row_scalar_bound consumes these two inequalities and the original top-six/bottom-ten inequality directly. The other branch uses the same three row slacks, full spectral gaps and the existing norm/mass mixture theorem.

For the continuous reduction let g_i=l_i-l_(i+1) for i<N-1 and g_(N-1)=l_(N-1). Nonnegativity follows from ordering. The spectrum is the sum of g_i times the step supported on the first i+1 entries. Middle gaps have 5<=i<N-10. Concentrating their total mass at any one such index leaves the fifteen boundary gaps unchanged. Every middle step has the same K1 image, with zero diagonal and off-diagonal entries -1, so this redistribution preserves the literal matrix and the three row slacks. The existing mixture theorem reconstructs the full spectrum and permits different constituent masses and zero middle mass.

For a concentrated term set j=i+1 and use sixteen gaps x at positions 1,2,3,4,5,j,N-9 through N. Put u=x6+...+x15, v=x5, h_k=x_k+...+x4 for 0<=k<5 and d_k=x6+...+x_(6+k) for 0<=k<9. Its mass is S=uN+vj+H-D and its square sum is Q=(2u+v)S-u(u+v)N+v(H+D)+H2+D2. The original rows give H3+D6<=3u-3v, H+D<=4u-6v and h0+D3<=2u-v. The literal K1 matrix becomes K_(u,v), with diagonal entries 2(u-d8), 2(u-d6), 2(u-d3) and upper off-diagonal entries -(v+h0+d7), -(v+h1+d5), -(v+h2+d4).

If u=0, row feasibility and nonnegative gaps force x=0. For u>0 and 2v<=u divide x by u and set w=v/u, with normalized heads h/u and tails d/u. The small-jump supplier applies for 0<=w<=1/4. For 1/4<=w<=1/2, actual_psd_nonflat_middle_energy bounds the full E=w(H+D)+H2+D2, including wD. Its two branches lie below (1+w)N-(2+w)^2/(4 theta), where theta=16(15N-8)/(15N-4)^2. Completing the square and using theta<=target(N) give the same norm bound.

For 2v>u set a=2v-u and b=2e5+3e15 in gap coordinates. The residual y=x-a*b is nonnegative and satisfies all three original row inequalities. Its low level is 4u-6v and 2y5 equals this level. The homogeneous estimate v(H+D)+H2+D2<=(4u-6v)(4u-5v) and the half-jump scalar envelope bound this residual using row feasibility alone. The argument uses no PSD premise for y. The bulk term a*b satisfies the rounded bound by the existing integer bulk maximum. Since x=y+a*b, norm addition and nonnegative homogeneity finish the concentrated term. The zero term and zero middle mass require no division.

The derivation reuses the repository's ActualPSDMoment, StructuralCone, ScalarEnvelopes, full-gap reconstruction and norm/mass mixture results. Hildebrand's PPT-from-spectrum work supplies the literal spectral-matrix context, not this rounded-purity derivation. This theorem concerns exactly the stated spectrum constraints; it gives no APPT sufficiency criterion, equality classification, physical attainment or literature novelty assertion.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ContinuousSpectrumAssembly.actual_k1_l4_purity_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment](ActualPSDMoment.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound](../QuadbitUniformSpectralBound.md)
