# The native three-coefficient common-plane consumer

## Abstract

Three independent native 3-by-5 and 5-by-3 coefficient matrices cannot produce a column isometry.

**Theorem 1.1 (No native column isometry from two independent triples).**

$$\forall M \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(5\right), Complex\right),\; \forall N \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(5\right), \operatorname{Fin}\left(3\right), Complex\right),\; (\operatorname{LinearIndependent}\left(Complex, M\right)) \Rightarrow ((\operatorname{LinearIndependent}\left(Complex, N\right)) \Rightarrow (\operatorname{conjTranspose}\left(\sum_{r : \operatorname{Fin}\left(3\right)} (\operatorname{kronecker}\left(M\left(r\right), N\left(r\right)\right))\right) \cdot \sum_{r : \operatorname{Fin}\left(3\right)} (\operatorname{kronecker}\left(M\left(r\right), N\left(r\right)\right)) \ne \operatorname{identity}\left(\operatorname{prod}\left(\operatorname{Fin}\left(5\right), \operatorname{Fin}\left(3\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation.native_three_refutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M range over all complex-linearly independent triples of 3-by-5 matrices, and N over all complex-linearly independent triples of 5-by-3 matrices. The Kronecker sum F has rows Fin 3 times Fin 5 and columns Fin 5 times Fin 3. The theorem says F*F cannot equal the identity on the latter carrier. There is no normalization, coefficient-kernel, plane, scalar cross-Gram, orthonormal embedding, or block-identity hypothesis.

NativeCoefficientWhitening.exact_whitening supplies an invertible coefficient change B, with M'=BM and N'=B inverse transpose N. It preserves the native Kronecker sum and independence of M, and derives sum_r M'(r)*M'(r)=I_5. Thus the coefficient-first stack S of M' is injective. CommonCoefficientPlane.common_plane then supplies one complex two-dimensional plane L neutral in the full sesquilinear pairing for every Hermitian T satisfying S*(T tensor I_3)S=0.

For each l,m in Fin 3, expansion of F*F gives the compression-kernel block T_lm(r,s)=(N'(r)*N'(s))_lm-delta_rs delta_lm. The compression is complex-linear and preserves conjugate transpose. Hence the Hermitian real and imaginary parts of each T_lm are both in the kernel; applying the same simultaneous plane to both parts proves full pairing neutrality for T_lm, including off-diagonal l,m.

Transport L by the explicit WithLp linear equivalence to EuclideanSpace, choose an orthonormal basis indexed by Fin 2, and write its columns as V. This constructs V*V=I_2. Define W_j,(r,l)=N'(r)_j,l and P=W*W on Fin 3 times Fin 3. With C=V tensor I_3, the neutral block equations give C*PC=I on Fin 2 times Fin 3. Rank multiplication bounds give rank(C*PC)<=rank(P)<=rank(W)<=5, whereas the identity on Fin 2 times Fin 3 has rank six, a contradiction.

This theorem addresses the exact independent-family k=3 case. The event definition also permits k=2 and is not refuted here. Reduction from unrestricted triples to a minimal independent decomposition, positive scalar normalization, and the original event with its eight dimension premises and both Gram implications are separate obligations. No classification, optimality, or resolution of that full event follows from this statement alone.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation.native_three_refutation`
- Dependency: [D5/S3/Quantum/Algebra/CommonCoefficientPlane](CommonCoefficientPlane.md)
