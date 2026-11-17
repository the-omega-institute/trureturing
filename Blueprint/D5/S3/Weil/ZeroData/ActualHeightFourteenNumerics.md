# Complete Signed Zeta Resolvent Estimate

## Abstract

Complete Signed Zeta Resolvent Estimate

**Theorem 1.1 (Complete Signed Zeta Resolvent Estimate).**

$$\frac{66493177}{143006288128704000} + \frac{4}{12649365729} \cdot \mathit{EulerGamma} - \frac{\operatorname{log}\left(2\right)}{1816214400} - \frac{9487}{40477970332800} \cdot \operatorname{log}\left(\pi\right) + \frac{\operatorname{Re}\left(\frac{-\operatorname{deriv}\left(\mathit{riemannZeta}, 6\right)}{\operatorname{riemannZeta}\left(6\right)}\right)}{3990729600} - \frac{\operatorname{Re}\left(\frac{-\operatorname{deriv}\left(\mathit{riemannZeta}, 8\right)}{\operatorname{riemannZeta}\left(8\right)}\right)}{3555377280} + \frac{\operatorname{Re}\left(\frac{-\operatorname{deriv}\left(\mathit{riemannZeta}, 10\right)}{\operatorname{riemannZeta}\left(10\right)}\right)}{6739588800} - \frac{\operatorname{Re}\left(\frac{-\operatorname{deriv}\left(\mathit{riemannZeta}, 12\right)}{\operatorname{riemannZeta}\left(12\right)}\right)}{24711825600} + \frac{\operatorname{Re}\left(\frac{-\operatorname{deriv}\left(\mathit{riemannZeta}, 14\right)}{\operatorname{riemannZeta}\left(14\right)}\right)}{216459734400} \le \frac{72126772613108177}{151944181136748 \cdot 10^{17}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics.h14_evaluatedMass_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete von Mangoldt series is split at 64. Every omitted term is retained: positive coefficients use the integral tail, and negative coefficients use nonnegativity. Rational logarithm and Euler constant bounds yield the exact signed scalar upper bound consumed by h14Mass_upper and actual_height_gt_fourteen. The first Li mass is supplied by the original owner, and no height or mass conclusion is a premise.

**Theorem 1.2 (Concrete six-pole kernel bounds).**

$$\forall rho \in \mathbb{C},\; 0 < \operatorname{re}\left(\mathit{rho}\right) \Rightarrow \left(\operatorname{re}\left(\mathit{rho}\right) < 1 \Rightarrow \left(100 < \operatorname{im}\left(\mathit{rho}\right)^{2} \Rightarrow \left(0 < \operatorname{h14Weight}\left(\mathit{rho}\right) \land \left(\operatorname{im}\left(\mathit{rho}\right)^{2} \le 196 \Rightarrow \frac{345650537}{72636 \cdot 10^{18} + 763553532703907200} \le 2 \cdot \operatorname{h14Weight}\left(\mathit{rho}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics.h14_kernel_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The six shifts 0, 30, 56, 90, 132, and 182 are now consumed in this numerical owner. The generic Sector calculus supplies positivity and monotonicity; the exact six-pole evaluation gives the full lower constant with every sign and multiplicity preserved. The open-strip and height-ten premises are discharged by the existing complete zero-data source.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics.h14_evaluatedMass_upper`
- Truth anchor: `D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics.h14_kernel_bounds`
- Dependency: [D5/S3/Arith/GoldenResource/HarmonicGammaTail](../../Arith/GoldenResource/HarmonicGammaTail.md)
- Dependency: [D5/S3/Arith/GoldenResource/RobinRationalBasis](../../Arith/GoldenResource/RobinRationalBasis.md)
- Dependency: [D5/S3/Weil/ZeroData/ActualHeightFourteenSector](ActualHeightFourteenSector.md)
- Dependency: [D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds](ActualReciprocalSquareBounds.md)
