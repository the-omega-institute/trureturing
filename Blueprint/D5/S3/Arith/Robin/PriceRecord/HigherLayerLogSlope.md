# Uniform logarithmic slope of the actual higher-layer marginal

## Abstract

Uniform logarithmic slope of the actual higher-layer marginal.

For every natural j>=2 and real u>=2, S_j is the finite sum u+...+u^j, beta_j=log(1+1/S_j)/log(u). The source differentiates log(beta_j), proves S_j<=2u^j and uS_j prime>=j u^j, and bounds the reciprocal logarithm factor below by 4/5. It obtains logarithmicSlope>=j/3, integrates that inequality on the closed lower boundary, proves strict antitonicity, and constructs a finite decay endpoint. beta_nat reconciles the real formula with the existing goldenLayerMarginal at every prime and every positive layer.

**Theorem 1.1 (powerSum succ).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem powerSum_succ (j : ℕ) (u : ℝ) : powerSum (j + 1) u = powerSum j u + u ^ (j + 1)

**Theorem 1.2 (powerSum nonneg).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem powerSum_nonneg {u : ℝ} (hu : 0 ≤ u) (j : ℕ) : 0 ≤ powerSum j u

**Theorem 1.3 (last power le sum).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.last_power_le_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.last_power_le_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem last_power_le_sum {u : ℝ} (hu : 0 ≤ u) {j : ℕ} (hj : 1 ≤ j) : u ^ j ≤ powerSum j u

**Theorem 1.4 (powerSum pos).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem powerSum_pos {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 1 ≤ j) : 0 < powerSum j u

**Theorem 1.5 (powerSum geometric).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_geometric`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_geometric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem powerSum_geometric (j : ℕ) (u : ℝ) : (u - 1) * powerSum j u = u * (u ^ j - 1)

**Theorem 1.6 (powerSum le twice).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_le_twice`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_le_twice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem powerSum_le_twice {u : ℝ} (hu : 2 ≤ u) (j : ℕ) : powerSum j u ≤ 2 * u ^ j

**Theorem 1.7 (powerSum hasDerivAt).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem powerSum_hasDerivAt (j : ℕ) (u : ℝ) : HasDerivAt (powerSum j) (powerSumDerivative j u) u

**Theorem 1.8 (weighted last le).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.weighted_last_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.weighted_last_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem weighted_last_le {u : ℝ} (hu : 0 ≤ u) {j : ℕ} (hj : 1 ≤ j) : (j : ℝ) * u ^ j ≤ u * powerSumDerivative j u

**Theorem 1.9 (gain pos).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.gain_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.gain_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem gain_pos {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 1 ≤ j) : 0 < gain j u

**Theorem 1.10 (gain le inv pow).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.gain_le_inv_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.gain_le_inv_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem gain_le_inv_pow {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 1 ≤ j) : gain j u ≤ 1 / u ^ j

**Theorem 1.11 (beta pos).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem beta_pos {u : ℝ} (hu : 2 ≤ u) {j : ℕ} (hj : 1 ≤ j) : 0 < beta j u

**Theorem 1.12 (beta le inv pow log).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_le_inv_pow_log`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_le_inv_pow_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem beta_le_inv_pow_log {u : ℝ} (hu : 2 ≤ u) {j : ℕ} (hj : 1 ≤ j) : beta j u ≤ 1 / (u ^ j * log u)

**Theorem 1.13 (beta nat).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_nat`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem beta_nat {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j) : beta j (p : ℝ) = goldenLayerMarginal p j

**Theorem 1.14 (log beta hasDerivAt).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.log_beta_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.log_beta_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem log_beta_hasDerivAt {u : ℝ} (hu : 2 ≤ u) {j : ℕ} (hj : 1 ≤ j) : HasDerivAt (fun v => log (beta j v)) (-logarithmicSlope j u / u) u

**Theorem 1.15 (logarithmicSlope ge).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.logarithmicSlope_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.logarithmicSlope_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem logarithmicSlope_ge {u : ℝ} (hu : 2 ≤ u) {j : ℕ} (hj : 2 ≤ j) : (j : ℝ) / 3 ≤ logarithmicSlope j u

**Theorem 1.16 (beta continuousOn).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_continuousOn`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_continuousOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem beta_continuousOn {j : ℕ} (hj : 1 ≤ j) : ContinuousOn (beta j) (Set.Ici 2)

**Theorem 1.17 (log beta drop).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.log_beta_drop`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.log_beta_drop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem log_beta_drop {j : ℕ} (hj : 2 ≤ j) {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) : (j : ℝ) / 3 * log (v / u) ≤ log (beta j u / beta j v)

**Theorem 1.18 (beta strictAntiOn).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_strictAntiOn`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_strictAntiOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem beta_strictAntiOn {j : ℕ} (hj : 2 ≤ j) : StrictAntiOn (beta j) (Set.Ici 2)

**Theorem 1.19 (beta small endpoint).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_small_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_small_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem beta_small_endpoint {j : ℕ} (hj : 1 ≤ j) {η : ℝ} (hη : 0 < η) : ∃ v : ℝ, 2 ≤ v ∧ beta j v < η

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_continuousOn`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_le_inv_pow_log`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_nat`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_pos`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_small_endpoint`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_strictAntiOn`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.gain_le_inv_pow`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.gain_pos`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.last_power_le_sum`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.log_beta_drop`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.log_beta_hasDerivAt`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.logarithmicSlope_ge`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_geometric`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_hasDerivAt`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_le_twice`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_nonneg`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_pos`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_succ`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.weighted_last_le`
- Dependency: [D5/S3/Arith/GoldenResourceOptimalInteger](../../GoldenResourceOptimalInteger.md)
