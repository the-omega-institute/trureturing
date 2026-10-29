# Original four-current thermal resummation

## Abstract

Absolute resummation of the four original lattice-current blocks on the entire open coordinate polydisk.

Let D be the original integral even symmetric lattice datum, hD a proof that its real Gram matrix is positive definite, and i : Fin 4 to Fin D.rank the four labeled current directions. Every coordinate z(j) is complex with norm less than one; zero coordinates and signed cross Gram entries are allowed. Put q = product_j z(j), Q(beta) = chargeEnergy(D,beta).toNat and N(d) = oscillatorEnergy(d). The thermal coefficient is product_j z(j)^n(j) times actualFourCurrentCycleTrace(D,hD,i,n), the LinearMap.trace of the four original current grade compressions in their original order on the complete energy grade n(0).

**Definition 1.1 (Positive-frequency edge kernel).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.edgeKernel`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.edgeKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a labeled ordered edge e=(a,b), its arc is a<j<=b and its complement is the other side. Let s and t be the corresponding products of coordinates. The kernel is sum_r (r+1)*(s^(r+1)+t^(r+1))/(1-q^(r+1)), over every natural r. Both sides are nonempty for every actual matching edge, so their norms are less than one. The only denominator is 1-q^(r+1), whose nonvanishing follows from norm(q)<1.

**Definition 1.2 (Unpaired-current charge moment).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.chargeMoment`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.chargeMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite set S of slot positions the moment sums q^Q(beta) times product_(j in S) bilinear(D,unitCharge(i(j)),beta), over every integral charge beta. Slot labels remain distinct even when their current indices agree.

**Definition 1.3 (Ten-matching thermal value).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.thermalValue`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.thermalValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value is Zosc(D,q) times the sum over the actual ten PM4 partial matchings M of Theta_(unpaired M)(D,i,q) times product_(e in M) G(i(e.first),i(e.second))*K_e. Here Zosc is the ordinary unsigned sum of q^N(d). The empty edge assignment is the unique function on an empty edge type; no factorial or quotient identifies edge slots.

**Theorem 1.4 (Ordinary oscillator Euler product).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.ordinary_oscillator_hasProd`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.ordinary_oscillator_hasProd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original lattice datum and norm(q)<1, HasProd of ((1-q^(m+1))^(-1))^rank, indexed by all natural m, has value sum_d q^N(d). Absolute convergence uses the accepted signed occupation theorem only through equality of norms. Finite Finsupp power algebra identifies the unsigned monomial with q^N(d). The generic ordinary occupation Euler supplier is then applied and its finite color factors are collected; the signed Euler value is never substituted.

**Theorem 1.5 (Absolute original-grade thermal family).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.original_four_current_thermal_normSummable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.original_four_current_thermal_normSummable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,hD,i,z with all four coordinate norms below one, the norm of product_j z(j)^n(j)*actualFourCurrentCycleTrace(D,hD,i,n) is summable over every natural grade quadruple. The source is the actual labeled countable sum Sigma_(M:PM4) Charge D times Exponent D times (edgeParam M to Nat times Fin 2 times Nat). Each edge stores r, its independently labeled orientation, and its winding k, with positive frequency r+1.

The source grade at j is Q(beta)+N(d)+sum_e (r_e+1)*(k_e+sideIndicator(e,j)). Natural-power identities factor its coordinate monomial into q^Q(beta), q^N(d), and the actual marked edge terms. This step takes no inverse of a coordinate or of q and therefore preserves 0^0=1. Products of the accepted bilinear charge bounds are dominated by the accepted charge Gaussian moment of degree equal to the number of unpaired positions. The ordinary occupation norm supplier and the accepted marked_summable theorem for each of the two edge orientations give the other independent factors. Their nonnegative tensor product and the finite PM4 sum establish absolute convergence of the whole ungrouped source before complex rearrangement or fiber pushforward.

For a fixed n, the exact source fiber is equivalent to bounded structural data followed by IntegerFiber D t. The original matching_parameter_bounds supplier places every positive frequency in Fin(max4(n)+1), every winding and t in Fin(min4(n)+1), and Q(beta) below min4(n). The original charge_cutoff_nat converts that last bound into precisely the original positiveChargeCutoff. The maps preserve all additive grade equations and every labeled edge; they do not filter by nonzero weight or subtract charge energy to fabricate residual fibers. Summing the actual ordinary occupation fiber yields Nat.card(IntegerFiber D t), recovering precisely the original chargeWeight. The finite actual_four_current_grade_trace theorem then identifies the grouped source with the literal original trace.

**Theorem 1.6 (Evaluated original four-block thermal series).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.original_four_current_thermal_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.original_four_current_thermal_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original thermal family has HasSum equal to thermalValue D i z on the entire open four-polydisk. After global source absolute convergence, independent charge, ordinary occupation and labeled-edge products can be evaluated. Each edge value applies the accepted marked_sum theorem separately to its two Fin 2 orientations. Finite matching sums and the exact original-grade fiber pushforward give the stated value. Negative cross Gram factors keep their signs in this value and enter absolute values only in convergence bounds.

**Theorem 1.7 (Zero at the coordinate origin).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.thermal_value_all_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.thermal_value_all_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The all-zero coordinate value is zero. On the original series, only the all-zero grade can survive its natural-power monomial, and the original zero-mode trace is zero there. Mixed zero-coordinate faces remain in the theorem domain: min4(n)=0 leaves the singleton t=k=0, permits positive frequencies when max4(n)>0, and retains perfect-matching contributions. Equal frequencies and repeated current indices never merge independent labeled slots.

The finite current normalization and original field constructions retain the Bakalov--Kac attribution of the finite trace supplier. This result is the ordinary chiral lattice thermal identity on a coordinate polydisk. Annular continuation of the four-point function, modular covariance, sewing, complete nonchiral CFT, Monster realization, string consistency and an AdS/CFT correspondence require additional results.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.chargeMoment`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.edgeKernel`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.ordinary_oscillator_hasProd`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.original_four_current_thermal_hasSum`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.original_four_current_thermal_normSummable`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.thermalValue`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal.thermal_value_all_zero`
- Dependency: [D5/S3/Combinatorics/Partitions/AnalyticIntegerOccupation](../../Combinatorics/Partitions/AnalyticIntegerOccupation.md)
- Dependency: [D5/S3/Combinatorics/Partitions/AnalyticOddOccupation](../../Combinatorics/Partitions/AnalyticOddOccupation.md)
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeFourCurrentTrace](LatticeFourCurrentTrace.md)
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentThermal](LatticeTwoCurrentThermal.md)
- Dependency: [D5/S3/VertexAlgebra/Sewing/CanonicalFullChargeLoop](../Sewing/CanonicalFullChargeLoop.md)
