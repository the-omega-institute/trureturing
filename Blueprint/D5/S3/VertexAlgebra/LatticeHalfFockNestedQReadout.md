# Nested Ordered Q Readouts

## Abstract

The three nested fractional products retain one actual labelled Laurent numerator.

**Theorem 1.1 (All three nested coefficients are extracted from the same actual ternary numerator).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockNestedQReadout.actual_nested_ordered_readouts`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockNestedQReadout.actual_nested_ordered_readouts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Let J be the actual half-frequency current, A=T_gamma(a) and B=T_delta(b), where a,b are arbitrary original source states. Choose K from the actual finite Laurent carrier theorem. For signed d,r,n, an arbitrary actual tensor input x and complex linear functional phi, take the degree-T slice of the original six-order cleared numerator, where T=L+M+N-d-r-n-3 and L,M,N are the three original clearing orders. The same labelled Laurent polynomial P gives all three nested readouts. All charges, both theta signs and unreduced signed lifts remain in scope.

The first coefficient is Q_r^(gamma+1)(T_(gamma+1)(h_d a),B)[n]x. The second is Q_(d-j)^1(J,Q_(r+j)^gamma(A,B))[n]x. The third is Q_(d+r-j)^gamma(A,T_(delta+1)(h_j b))[n]x, for every signed j. The first and third use the actual current inverse to identify the source current insertion. Their inner cutoffs are respectively vectorFrequencyBound(a)+1 and vectorFrequencyBound(b)+1. The second uses K for its inner source pair. Every outer cutoff is arbitrary.

finiteQReadout uses the literal finite fractional sum and both complete residue halves. The forward range is max(0,-ord(Bx)-n+ell); the reverse range is max(0,-ord(Ax)). In a nesting, A or B here can be the complete intermediate Q field. Its order is taken before splitting its inner residue. Each inner range is then recomputed on the actual intermediate vector. No two unbounded chamber sums are separated or exchanged.

nestedLeftReadout and nestedRightReadout retain all four resulting triple words and their signs. rationalTripleReadout reads each word from the supported permutation expansion of P divided by the original clearing polynomial. The third nesting exchanges current and first-source labels in the readout while leaving P and its denominator unchanged. Every summand has total mode index d+r+n; hence its total exponent is -d-r-n-3 and the same slice T applies to every fractional correction, residue offset and j.

This theorem identifies nested ordered rational coefficients. It does not identify the collision-coordinate Taylor coefficients, prove the fractional cocycle cancellation, or establish Lambda_tar=0. The Taylor antidiagonal L+M+N-d-r-2, integration of the signed lift carry with the collision charts, residual-free DE-L, universal negative first-word transport and all-charge induction remain separate obligations. GroundFirst remains an independent final lifting base. No target vacuum, positive definiteness, energy eigenstate, or compatibility law is assumed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockNestedQReadout.actual_nested_ordered_readouts`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockClearedTaylorReadout](LatticeHalfFockClearedTaylorReadout.md)
