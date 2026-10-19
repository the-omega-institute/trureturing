# Actual K1 and L4 spectral purity

## Abstract

Continuous literal-K1 and top-six/bottom-ten purity bound with natural rounding.

The Lean #print axioms output for actual_k1_l4_length52_purity_bound is [propext, Classical.choice, Quot.sound]. The literal 52-dimensional conclusion is checked by the kernel, independently of the source-level rational arithmetic checks.

**Theorem 1.1 (Unrestricted length-52 actual K1 plus L4 endpoint).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ContinuousSpectrumAssembly.actual_k1_l4_length52_purity_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ContinuousSpectrumAssembly.actual_k1_l4_length52_purity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any antitone nonnegative l:Fin 52 to Real with sum l_i=1, assume sum of its first six entries is at most sum of its last ten entries. Assume the literal matrix [[2l51,l50-l0,l48-l1],[l50-l0,2l49,l47-l2],[l48-l1,l47-l2,2l46]] is PSD. Then sum l_i^2<=5/243. There is no K2 premise and no finite, two-level or endpoint ansatz for l. Zero coordinates, repeated values and singular matrices are included. Proof shape: content. Admission basis: escape-witness; the new two-ninths joint moment closes the small-jump gap at length 52 and the exact continuous concentration supplies the unrestricted inference.

Normalize a nonzero block by its low level: S=52+w*j+H-D and Q=(2+w)S-52(1+w)+E. The zero low level is handled directly and forces the nonnegative row-feasible coefficient vector to vanish. For 0<=w<=2/9, shift all five heads by w and apply the new moment. The shifted L4 budget is 5w+H+D<=4-w. Its exact transport gives Q<=(20/9)S-60, and (5/243)S^2-Q>=(5/243)(S-54)^2. For 2/9<=w<=1/2, combine C(w) with Z(w)=(4-6w)(4-5w); the threshold Theta=52(1+w)-(243/20)(2+w)^2 dominates C on [2/9,7/16] and Z on [7/16,1/2], by kernel polynomial identities. Square completion gives the block bound.

For the large jump subtract (2v-u) times the original bulk coefficient vector, whose spectrum is (5^j,3^(52-j)). The residual is nonnegative by the L4 defect budget and has low level 4u-6v and half-jump. It need not be PSD: only the derived row constraints and the mass-only energy estimate are used. The half-jump ratio is bounded by 25/(24*51)<5/243; the bulk ratio is at most 16/(15*52)<5/243 by the identity 16(3N+2j)^2-15N(9N+16j)=(3N-8j)^2. The Euclidean norm cone is closed under addition and nonnegative scaling, including the zero residual.

For an arbitrary ordered spectrum, its nonnegative adjacent gaps reconstruct it exactly. Concentrating only the middle gaps preserves all boundary gaps, the actual K1 matrix and all three derived row readouts, including the exact first-six/last-ten inequality. The existing mixture_transfer theorem and norm cone addition then transport the block bound to the original l. This is an upper bound under necessary spectral constraints, not a characterization of APPT and not an equality or global uniqueness theorem. The inner-polytope formula and attaining spectrum (3,1,...,1)/(N+2) belong to Ahiable–Kothakonda–Winter, arXiv:2608.03390v2. Only the unrestricted upper-bound inference is a candidate addition; physical composition and literature priority require their own evidence.

**Theorem 1.2 (Rounded purity for every dimension at least 56).**

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

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ContinuousSpectrumAssembly.actual_k1_l4_length52_purity_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ContinuousSpectrumAssembly.actual_k1_l4_purity_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment](ActualPSDMoment.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound](../QuadbitUniformSpectralBound.md)
