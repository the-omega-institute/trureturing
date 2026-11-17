# Signed Boolean-cube moments

## Abstract

Signed Boolean moments realize centered singular series and their cubic and fourth identities.

**Theorem 1.1 (Centering commutes with injective transport).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel.centerFinite_image`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel.centerFinite_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite subset centering transform commutes with transporting all subsets along an injective map.

Let the coordinates on finite subsets B be Y(d,B)=s*1[d in B]-1. Boolean incidence-algebra Mobius inversion prescribes the uncentered moments C(D)/s^|D|. Its inverse-zeta identity gives the required signed functional, with no positivity assertion. The commutative-ring centred product expansion applies directly in the algebra of cube functions to identify square-free moments. The resulting formal values supply the coefficient identities used in interval moment bounds.

**Theorem 1.2 (The formal second value).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel.formal_second_moment_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel.formal_second_moment_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For normalized empty and singleton data and nonzero s, the second coefficient moment is its ordered distinct-index moment plus (s-1) times the sum of the product of the two coefficients.

**Theorem 1.3 (The formal cubic value).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel.formal_third_moment_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel.formal_third_moment_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cubic coefficient moment is the ordered distinct triple sum, plus (s-2) times the three distinct pair sums formed by multiplying two coefficient functions, plus (s-2)(s-1) times the full diagonal coefficient sum. This is quadratic_third_moment_eq applied with a=s-2 and b=s-1.

**Theorem 1.4 (The formal fourth pairing defect).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel.formal_fourth_pairing_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel.formal_fourth_pairing_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fourth moment minus its three products of second moments equals the distinct fourth pairing defect, plus the six repeated-pair terms with coefficient s-2, the three pair-pair terms with coefficient (s-2)^2, the four triple-singleton terms with coefficient (s-2)^2-2(s-1), and the full diagonal with coefficient (s-2)^2(s-1)-2(s-1)^2. The equality applies quadratic_fourth_pairing_defect without reclassifying index patterns.

**Theorem 1.5 (Interval values as finite coefficient moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel.Phi_eq_formalMoment`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel.Phi_eq_formalMoment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On any finite set containing all interval shifts, Phi equals the general formal coefficient moment with the interval indicator coefficients and singular series transported by the inclusion into the natural numbers. This equality holds for arbitrary s and arbitrary singular-series data.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel.Phi_eq_formalMoment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel.centerFinite_image`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel.formal_fourth_pairing_defect`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel.formal_second_moment_eq`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel.formal_third_moment_eq`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ArithmeticTransferDefs](ArithmeticTransferDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredProductExpansion](CentredProductExpansion.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticFourthDefect](QuadraticFourthDefect.md)
