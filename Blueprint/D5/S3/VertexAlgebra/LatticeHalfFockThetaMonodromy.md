# Original source reflection and physical mode selection

## Abstract

Native all-state theta monodromy

Only the original lattice data and invertibility of its integral Gram determinant are assumed. The field is the original Ytw on the full finite-support lattice carrier. Theta negates the source charge and every source oscillator; no reflection of the target ground vector is substituted.

**Theorem 1.1 (The original theta field is literal coordinate sign monodromy).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockThetaMonodromy.Ytw_theta`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockThetaMonodromy.Ytw_theta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every original state u and integer E, Ytw(theta(u))[E]=(-1)^E Ytw(u)[E]. Integer powers are genuine zpow, including negative exponents. The auxiliary correction sign map fixes the shift coordinate none, fixes scalar coefficients and negates oscillator coordinates some(i). Singleton charge linearity and pair-derivation anticommutation prove the sign law by induction on the actual correctionWord recursion. Actual optionEquivLeft and shiftCoefficients then prove Corr(-a,sigma(p))[s]=sigma(Corr(a,p)[s]), with repeated colours and arbitrary finite source polynomials preserved. Actual normalWord_flattened and flatTerm_finite permit extracting the charged sign from each pointwise finite tuple sum. The original jetShift is word length plus twice the original word weight: its cons increment is exactly 2n+3. Original leftAction and rightAction retain the physical mode<0 split. The two oscillator-word signs cancel, and every correction shift contributes an even exponent. Source Finsupp linearity completes the full statement.

**Theorem 1.2 (An incompatible source eigenvalue forces the actual coefficient to vanish).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockThetaMonodromy.Ytw_coefficient_selection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockThetaMonodromy.Ytw_coefficient_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

If theta(u)=lambda u and lambda differs from (-1)^E, the actual operator coefficient Ytw(u)[E] is zero. This consumes all-state native monodromy and scalar faithfulness over the complex numbers, without an assumed twisted-module or Jacobi law.

**Theorem 1.3 (Theta-even and theta-odd original sources select opposite cover parity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockThetaMonodromy.Ytw_even_odd_selection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockThetaMonodromy.Ytw_even_odd_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Every odd integer cover coefficient of a theta-even original source vanishes, and every even integer cover coefficient of a theta-odd original source vanishes. These statements include negative cover indices. They are consumed by the native physical-mode theorem.

**Theorem 1.4 (Physical integer and half-integer modes belong to the source theta sector).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockThetaMonodromy.Ytw_physical_mode_selection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockThetaMonodromy.Ytw_physical_mode_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For alpha and beta in {0,1}, an original theta eigenstate of eigenvalue (-1)^alpha has zero coefficient at E=-2k-beta-2 whenever alpha differs from beta. Thus the physical mode k+beta/2 can occur only in the matching original source sector. The cover exponent and the additive minus-two convention are unchanged.

The correction-polynomial anticommutation and actual finite normal-word calculation supply the substantive new proof. The charged monodromy and ordinary theta automorphism are reused, not reproved or claimed as new mathematical results. This is a classical twisted lattice construction, not a novelty claim.

This proves native all-state theta monodromy and its coefficient selection only. Full twisted Jacobi, full CFT, fusion and anomaly structures, Monster moonshine, a complete formalization of string theory, spacetime emergence and AdS/CFT remain open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockThetaMonodromy.Ytw_coefficient_selection`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockThetaMonodromy.Ytw_even_odd_selection`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockThetaMonodromy.Ytw_physical_mode_selection`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockThetaMonodromy.Ytw_theta`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockAllStateField](LatticeHalfFockAllStateField.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeInvolution](LatticeInvolution.md)
