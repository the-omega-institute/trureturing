# Actual boundary-price exchange geometry

## Abstract

Actual boundary-price exchange geometry.

**Theorem 1.1 (Nonnegative local price bound).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.priceLip_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.priceLip_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural j and real a>=2, priceLip(j,a) is nonnegative. This sign is used in the normalized actual boundary-price cost.

**Theorem 1.2 (Variation of the real layer price).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.price_variation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.price_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For j>=1 and a>=2, the difference between beta(j,x) and beta(j,y) for x,y>=a is at most priceLip(j,a)*abs(y-x). The logarithmic derivative estimate is uniform on the whole ray, including its lower endpoint.

**Theorem 1.3 (Separation on every original record).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.uniform_coarse_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.uniform_coarse_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each fixed j>=2 a single positive threshold precedes every m>=2 and every original mu>0 with the full strict predecessor record. With P=largestPrime(m) and Q=layerPrime(m,j), P>=4, Q>=4, Q<=P/8, the second layer is strictly below P/2, and log(Q/2)>=log(P)/(4*j). No optimizer at a replacement price is substituted.

**Theorem 1.4 (Price obstruction from four actual prime pools).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.actual_boundary_price_from_pools`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.actual_boundary_price_from_pools` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix j>=2. One positive threshold precedes all original positive-price full records. With P=largestPrime(m), Q=layerPrime(m,j), K=ceil(P^(19/(40*j))), four actual prime sets of cardinality K in the stated lower and upper windows give abs(beta(j,Q)-beta(1,P))<=priceLip(j,Q/2)*w+priceLip(1,P/2)*v+(8*j/K)*(beta(1,P)+priceLip(1,P/2)*v). The windows have independent widths w<=Q/2 and v<=P/2, and the higher-layer bands retain their neighboring-layer constraints. The strict predecessor exchanges use original valuations and bounded rounding costs.

**Theorem 1.5 (Exact prime cardinalities on both sides).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.counted_higher_pools`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.counted_higher_pools` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A supplied two-sided short-interval count and capacity K+1 give two finite sets of exactly K distinct actual primes near a natural endpoint N. The lower set retains the closed upper endpoint; the upper set excludes N. The extra unit pays for deleting a possible prime endpoint. This result uses the count supplier directly.

**Theorem 1.6 (Strict upper mass crossing).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.subset_just_above`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.subset_just_above` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite pool with total mass strictly above t has a subset with mass strictly above t and at most t+H. Exact partial-sum equalities are retained on the strict side. Exact Lean telescope: {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ) {t H : ℝ} (ht : 0 ≤ t) (hH : ∀ a ∈ S, f a ≤ H) (htotal : t < ∑ a ∈ S, f a) : ∃ D ⊆ S, t < ∑ a ∈ D, f a ∧ (∑ a ∈ D, f a) ≤ t + H

**Theorem 1.7 (Strict lower mass crossing).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.subset_just_below`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.subset_just_below` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite pool with total mass at least positive t has a subset with mass strictly below t and deficiency at most H. The case of total mass exactly t is included. Exact Lean telescope: {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ) {t H : ℝ} (ht : 0 < t) (hH : ∀ a ∈ S, f a ≤ H) (htotal : t ≤ ∑ a ∈ S, f a) : ∃ U ⊆ S, (∑ a ∈ U, f a) < t ∧ t ≤ (∑ a ∈ U, f a) + H

**Theorem 1.8 (Original signed finite exchange).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.exchange_mass_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.exchange_mass_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For disjoint distinct-prime deletion and insertion sets with strictly smaller insertion logmass, the original full record gives the signed comparison. The complete term -mu*(logMass D-logMass U) is retained, without assuming a sign for the comparison price or the marginal fees. Exact Lean telescope: {m : ℕ} {mu lambda h : ℝ} (hm : 0 < m) (hrecord : FullRecord m mu) (D U : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hU : ∀ p ∈ U, p.Prime) (hDvd : ∀ p ∈ D, p ∣ m) (hdis : Disjoint D U) (hbalance : logMass U < logMass D) (hupper : (∑ p ∈ D, goldenLayerMarginal p (m.factorization p) * log p) ≤ lambda * logMass D) (hlower : h * logMass U ≤ ∑ p ∈ U, goldenLayerMarginal p (m.factorization p + 1) * log p) : h * logMass U < lambda * logMass D - mu * (logMass D - logMass U)

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.actual_boundary_price_from_pools`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.counted_higher_pools`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.exchange_mass_bound`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.priceLip_nonneg`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.price_variation`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.subset_just_above`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.subset_just_below`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.uniform_coarse_geometry`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope](HigherLayerLogSlope.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/LogarithmicLayerRigidity](LogarithmicLayerRigidity.md)
