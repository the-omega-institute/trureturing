# From native Laurent coefficients to the signed-mode identity

## Abstract

Four-point crossing for arbitrary Fock occupations

**Theorem 1.1 (Fourier identities after cancelling the chart scales).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.native_laurent_crossing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.native_laurent_crossing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a positive definite rank-24 lattice with unit Gram determinant. Form four words from a list of distinct marks in a finite decidable type, with a puncture, colour and natural mode index at each mark. The words tensored with nonzero ground vectors have natural weights H, K, L, J with J = H + K + L − s − 2 for an integer s. For every real 1/2 < x < 1 and every charge class, evaluate native A, B and D at their chart parameters. The native D value is 2⁻¹² times the Fourier sum of A. The native B value multiplied by x^(s+2) is 2⁻¹² times the quadratically signed Fourier sum of A. Group the lifted scales by puncture and use homogeneity to express the products in terms of the four weights. On including the Laurent powers and phases, A and D have the common nonzero scalar −i(1−x)³x^(−s−5). The B scalar is −i(1−x)³x³. The inverse twelfth power of the A period root is x⁶, so the B comparison leaves x^(s+2). `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeLaurent.native_laurent_fourier_overlap`

**Theorem 1.2 (Exact B and D channel transport).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.nativeLaurent_eq_transported_channels`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.nativeLaurent_eq_transported_channels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any lattice datum, natural weights H, K, L, J, signed modes m, n, r with J = H + K + L − (m+n+r) − 2, four oscillators, any charge class a and any complex t, native B at t is the slit B channel at t. The sum of native D at t over classes b weighted by the quadratic sign of b+a is the D-lip channel at t with upperA = true, choosing the upper A continuation and the lower D lip. Unfold both channels and use the signed output relation to identify their literal lowering cutoff with the natural subtraction J−1. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelB`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChannel`

**Theorem 1.3 (Real A/B and A/D crossing for occupation words).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.occupation_word_real_crossing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.occupation_word_real_crossing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the four homogeneous marked words under the same lattice, marking and ground hypotheses as the native Fourier identities. Use any signed modes m, n, r with s = m+n+r and the same output relation for J. For every real 1/2 < x < 1 and output class b, slit A at 1−x⁻¹ equals 2¹² x^(s+2) times slit B at x and equals the selected lower D-lip channel at x⁻¹. The B comparison uses symmetry of the Fourier sign. In the D comparison, exchange the two finite charge sums and apply the translated quadratic Gauss sum. Its factor 2¹² cancels the Fourier normalization and its remaining signs give the slit A charge combination. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.native_laurent_crossing`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.nativeLaurent_eq_transported_channels`

**Theorem 1.4 (The original signed-mode identity for occupation monomials).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.arbitrary_occupation_identityK`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.arbitrary_occupation_identityK` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let D have positive definite real Gram form, unit Gram determinant and rank 24. At each of P, Q, R, S choose any finitely supported occupation exponent bᵢ, a natural weight eᵢ and a nonzero actual ground vector gᵢ. Require the coefficient-one monomial of exponent bᵢ tensored with gᵢ to be an actualTensorL0 eigenvector of weight eᵢ. For all integer m, n, r with e_S = e_P + e_Q + e_R − (m+n+r) − 2, identityK holds on those four monomials. For every output charge, its Fourier- and quadratic-signed A sum equals 2¹² times B minus the translated quadratic-sign sum of D. Expand each exponent into its multiset of mode occurrences and label the positions in the four tagged lists by distinct finite indices. Filtering by puncture recovers each word and counting mode multiplicities recovers its monomial. The real A/B identity accumulates at x = 3/4 in the double slit. Inverting x gives a real germ at t = 4/3 for A and the lower D lip. Continue that germ to the interior A/D overlap and glue the slit charts. The three Laurent expansions of the common germ yield identityK by residue balance. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.occupation_word_real_crossing`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.slit_AD_overlap`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.identityK_of_slitChart_crossing`

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChannel`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.slit_AD_overlap`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeLaurent.native_laurent_fourier_overlap`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.identityK_of_slitChart_crossing`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelB`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.arbitrary_occupation_identityK`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.nativeLaurent_eq_transported_channels`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.nativeLaurent_eq_transported_channels`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.native_laurent_crossing`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.native_laurent_crossing`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.occupation_word_real_crossing`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport.occupation_word_real_crossing`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeLaurent](OriginalFourMNativeLaurent.md)
