# Direction, amplitude, and one global orientation

## Abstract

Pure rigidity of the same original total relation

The carrier, Jordan product, cone, norm and total relation D are exactly those in OriginalDContract. A pure label is (0,x). The function lift(n,a) = a.vector + a.scalar n is a known evaluation coordinate map; it does not change D or assert any linearity of D.

PureSuppliers consists of skew symmetry, zero output for pairs on the same vector axis, the zero finite-difference residual, the squared determinant bound for every unit vector n and every original pair, and exact SO(2) mixing of the two labels. For the same arbitrary total D, OriginalDContract.p2_skew supplies skew symmetry from P2, collinear_zero supplies the axis identity from P2 and PB, pb_iff_finite_difference supplies the residual identity from literal PB, and label_rotation supplies label mixing from P2 and PB. Its second label c b - s a is exactly (-s) a + c b. Label mixing is not separate additivity or scalar homogeneity of D.

For the bound, take the actual original evaluation with mass one and vector n. The condition n dot n = 1 makes it positive. Direct expansion of the known Jordan product gives alpha_n(a Jordan b) = lift(n,a) dot lift(n,b). Applying OriginalDContract.p2_determinant_bound and the usual cross-dot-cross identity therefore gives the required squared lifted-cross bound. Only known coordinates are expanded; every D value remains the same original value. The full P2 premise still quantifies over all positive masses and vectors.

CommonNonunitPerpendicular is a Euclidean identity: any two vectors have a common nonzero perpendicular whose squared length is not one. TwoAxisFiniteRotation.unit_perpendicular_pair supplies a unit vector n perpendicular to the EuclideanSpace images of both original vectors. The inverse coordinate map gives v with v dot v = 1, and z = 2v has z dot z = 4 and the required two zero dot products. This adaptation reuses the original geometry existence proof and introduces no assumption on D or physical realization.

For nonorthogonal pure labels, a finite real root diagonalizes their two-label Gram matrix. Writing A = x dot x, B = y dot y and C = x dot y, the C nonzero branch chooses R = sqrt((A-B)^2 + 4 C^2), t = (B-A+R)/(2C), r = sqrt(1+t^2), c = 1/r and s = t/r. Then u = c x + s y and v = -s x + c y are perpendicular, c^2+s^2 = 1, and u cross v = x cross y. The label-rotation identity retains the same original D value. The C zero branch uses the unchanged pair.

For a nonzero orthogonal pair, the finite difference at third label zero gives y Jordan D(x,y) = 0. Swapping x and y supplies the second zero face. Hence the output scalar vanishes and its vector lies on the normal line spanned by x cross y. This is the direction argument; determinant positivity alone is not used as a substitute for it.

For amplitude, keep the inner pair and its coefficient k fixed. Put A = x dot x, B = y dot y, Y = sqrt(B), r = sqrt(l^2 A+1), n = (-l/r)x + y/(rY), and c = (r,l x), for an arbitrary finite real l. The same-axis identity gives D((0,x),c) = 0. The finite difference says that the two actual outer outputs differ by (0,2 l A y). Their squared evaluation bounds are both A/r^2+k^2 A B. Combining the two bounds gives (1-k^2) l^2 A B <= 1+k^2 B. If k^2 < 1, one explicit finite square-root choice of l contradicts this inequality. No limit or scaling of an unknown output is used.

For sign comparison in a fixed nonunit row x, take perpendicular directions y and z. The finite difference identifies the two outer outputs associated with y +/- k(x cross y) and z +/- l(x cross z). Pairwise saturation identifies their squared lengths with squared cross lengths. The difference of those squared cross lengths is 4(1+k l A)(l-k)(y dot z)(x dot (y cross z)). With k^2=l^2=1, opposite signs would force A=1 whenever the last two factors are nonzero. A finite intermediate direction y+t(x cross y), chosen beyond two explicit affine roots, removes the transverse restrictions.

A common nonunit perpendicular connects any nonunit row to a fixed nonunit reference row. Skew symmetry gives the reverse orientation. This first fixes all orthogonal pairs with at least one nonunit vector. For an orthonormal pair x,y, let w=x cross y. If the remaining pair had sign -e, the independently known nonunit value is D(x,2y)=(0,2e w). The finite difference then equates the outputs of (y-e w,2y+2e w) and (y+e w,2y-2e w). Both outer pairs are orthogonal with a nonunit vector, so their outputs are respectively (0,4x) and (0,-4x), a contradiction. Finally exact label orthogonalization covers arbitrary lengths and angles, and the same-axis zero identity covers all dependent and zero pairs.

**Definition 1.1 (Pure original labels).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.pure`

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.pure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pure label of x is the original element (0,x) of E.

**Definition 1.2 (Known evaluation coordinate map).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.lift`

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.lift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n in the original vector space and a in E, lift(n,a) is a.vector+a.scalar n.

**Definition 1.3 (Explicit basic original-D interfaces).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.PureSuppliers`

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.PureSuppliers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The five fields are skew symmetry, same-vector-axis zero output, the finite-difference identity, the squared unit-evaluation cross bound, and exact orientation-preserving label mixing. They organize the pure argument and are supplied from P2 and PB of that same arbitrary original D in global_pure.

**Definition 1.4 (Common perpendicular interface).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.CommonNonunitPerpendicular`

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.CommonNonunitPerpendicular` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every two vectors a,b there is a vector z, nonzero and of squared length different from one, perpendicular to both a and b.

**Theorem 1.5 (Saturation of every nonzero orthogonal pair).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.orthogonal_saturation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.orthogonal_saturation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every total D satisfying PureSuppliers and every nonzero orthogonal x,y, there is a real k with k^2=1 and D((0,x),(0,y))=(0,k(x cross y)). The finite-parameter estimate is the indispensable amplitude step.

**Theorem 1.6 (Saturation for arbitrary pure pairs).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.pure_pair_saturation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.pure_pair_saturation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under PureSuppliers, every pair x,y, including zero and dependent pairs, has some saturated coefficient k with k^2=1 and the stated cross output. At this stage k may depend on the pair.

**Theorem 1.7 (A transverse comparison fixes two row signs).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.transverse_sign`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.transverse_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under PureSuppliers, suppose x has squared length different from one, x is perpendicular to y and z, y dot z is nonzero, and x dot (y cross z) is nonzero. If the two original outputs have saturated real coefficients k and l, then k=l.

**Theorem 1.8 (Every nonzero perpendicular direction shares one nonunit row sign).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.nonunit_row_sign`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.nonunit_row_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under PureSuppliers, for nonzero x of squared length different from one and any nonzero y,z perpendicular to x, saturated coefficients of the corresponding original outputs are equal. The theorem has no extra angle or generic-position premise.

**Theorem 1.9 (The global sign under the basic pure interfaces).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.global_pure_of_suppliers`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.global_pure_of_suppliers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every total D satisfying PureSuppliers, and under CommonNonunitPerpendicular, there is one real e equal to +1 or -1 such that for every x,y the original value D((0,x),(0,y)) is (0,e(x cross y)). This conditional interface theorem is consumed by global_pure after both supplier interfaces are discharged.

**Theorem 1.10 (Original P2 and PB fix one sign for every pure pair).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.global_pure`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.global_pure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every arbitrary total D from the original E squared to E, if its actual directed complex two-label Gram matrices are positive semidefinite for every original positive evaluation and if its literal plus/minus phase-square balance PB holds, there exists one real e, e = 1 or e = -1, such that for every x,y in the original real three-space, D((0,x),(0,y)) = (0,e(x cross y)). The same sign covers all zero, proportional, nonorthogonal, unit/unit, nonunit and unequal-length pure inputs. PureSuppliers and CommonNonunitPerpendicular are derived within the proof and are not premises of this endpoint. No additivity, homogeneity, continuity, unit row, P3, NN, PY, R, CP or physical-realization premise is added. This is the pure prerequisite for the all-input classification; the scalar residual, classification converse, finite rotation transport and all stated consequences remain separate mathematical obligations.

## References

- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.CommonNonunitPerpendicular`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.PureSuppliers`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.global_pure`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.global_pure_of_suppliers`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.lift`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.nonunit_row_sign`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.orthogonal_saturation`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.pure`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.pure_pair_saturation`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalPureRigidity.transverse_sign`
- Dependency: [D5/S3/Geometry/TwoAxisFiniteRotation](../../Geometry/TwoAxisFiniteRotation.md)
- Dependency: [D5/S3/Quantum/SpinFactor/OriginalDContract](OriginalDContract.md)
