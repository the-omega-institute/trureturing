# Actual Laurent Windows

## Abstract

Finite Laurent windows retain the same actual six-order numerator and every actual tensor input.

**Theorem 1.1 (Each total-exponent slice has a finite rational carrier in all six orders).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockClearedTaylorReadout.actual_finite_laurent_carriers`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockClearedTaylorReadout.actual_finite_laurent_carriers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Let D be arbitrary LatticeData, hu a determinant-unit witness, i a current label and a,b arbitrary original source vectors. Choose the same order K supplied by actual_three_field_numerator. For every pair of signed lifts gamma,delta, every actual input x, every complex linear functional phi and every integer T, there is a labelled Laurent polynomial P_T. Its coefficient at e is phi applied to the actual cleared numerator at e if sum(e)=T, and zero otherwise. No positivity of exponents, energy eigenstate or target creative vector is assumed.

Write Q for the original weighted clearing polynomial and d for its degree, the sum of its three pair orders. For every permutation sigma and every integer exponent tuple e, the sigma-ordered expansion of P_T/Q has coefficient phi applied to the actual sigma-ordered J,A,B word at e if sum(e)=T-d, and zero otherwise. Both BJA and BAJ keep their actual operator order. The numerator remains labelled; permutations alter its supported embedding.

The proof restricts the coefficient function of an already supported Hahn carrier to a fixed total exponent. Its support is a subset of the existing support. Restriction commutes with multiplication by a homogeneous clearing factor with the exact degree shift. This is proved on the actual finite Hahn convolution antidiagonal. The simultaneous coordinate lower bounds from the six-order checkpoint make the restricted cleared numerator finite. Finsupp.ofSupportFinite constructs P_T with the literal coefficients, and supported field division proves the expansion identity.

This ternary carrier identification precedes Taylor substitution and residue extraction. The separate binary theorem below identifies a complete Q coefficient with its actual binary Taylor readout. The three nested ternary readouts, the antidiagonal residue degree, typed lift carry, target interchange, residual-free DE-L and the all-charge first-word induction remain additional obligations. GroundFirst is a separate final base question.

**Theorem 1.2 (The complete binary Q residue is the actual finite Taylor readout).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockClearedTaylorReadout.actual_binary_taylor_readout`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockClearedTaylorReadout.actual_binary_taylor_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Choose K from the same actual three-field locality checkpoint. For arbitrary signed gamma,delta,r,n with r<K, arbitrary actual input x and scalar linear functional phi, put A=T_gamma(a), B=T_delta(b), t=K-r-n-2 and k=K-r-1. The binary numerator is the actual labelled coefficient array (z-w)^K A(z)B(w)x. Its degree-t slice is finite. The theorem constructs its scalar Laurent polynomial P with coefficients phi(C_K(e)) at total exponent t and zero elsewhere; the same P works for every fractional lift s.

The scalar coefficient phi(Q_r^s(A,B)[n]x) equals the finite sum over coefficients of P of choose(e_A-s/2,k) P_e. Finsupp.linearCombination expresses exactly this finite weighted sum. All integer numerator exponents are admitted, including negative e_A. There is no vacuum, eigenstate, positive definiteness, product-preservation or interchange premise.

The proof embeds this very numerator into each of the two supported Hahn orders. Homogeneous restriction commutes with the clearing factor with shift K. Multiplication by its inverse kernel then identifies each ordered residue coefficient with the corresponding finite-polynomial coefficient. In the difference of the two chambers, forward support e_A>=k and reverse support e_A<0 give the single coefficient choose(e_A,k); the intervening nonnegative exponents vanish by the ordinary binomial bound. This calculation retains the complete reverse sign. Finite Vandermonde combines the fractional correction weights only after both actual carrier identities have been established.

Every residue appearing in the finite fractional sum has the same cleared total t because its two indices shift as r+ell,n-ell. This binary statement supplies no ternary reordering, no nested support or lift-carry identification, and no target Lambda cancellation. Those remain separate proof obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockClearedTaylorReadout.actual_binary_taylor_readout`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockClearedTaylorReadout.actual_finite_laurent_carriers`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockLeftCurrentTransport](LatticeHalfFockLeftCurrentTransport.md)
