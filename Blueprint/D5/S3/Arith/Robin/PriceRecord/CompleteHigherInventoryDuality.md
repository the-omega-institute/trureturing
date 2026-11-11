# All actual higher coordinates and exact complete loss

## Abstract

All actual higher coordinates and exact complete loss.

higherMass(n) is the sum over every actual prime factor of (v_p(n)-1 : Nat)*log(p). coordinates(n) contains exactly the prime pairs with 2<=j<=v_p(n), and its weight sum equals that mass. Canonical membership is reused from strict_layer_iff; equal prices are excluded. The literal completeSecondLayerLoss+completeHigherLayerLoss is converted to the union of all canonical and actual coordinates. The finite decomposition gives R=potential(«λ»bda)-inventoryGain(n)+«λ»bda*higherMass(n) on any finite superset of that union. Finite convex duality proves both signs using coordinatewise maximization and positive parts. This finite set never truncates n; even arbitrarily large actual negative-margin coordinates enter its actual inventory and loss.

**Theorem 1.1 (mem coordinates).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.mem_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.mem_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem mem_coordinates {n p j : ℕ} : (p, j) ∈ coordinates n ↔ p.Prime ∧ 2 ≤ j ∧ j ≤ n.factorization p

**Theorem 1.2 (sum coordinates).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.sum_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.sum_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem sum_coordinates (n : ℕ) (f : ℕ × ℕ → ℝ) : ∑ c ∈ coordinates n, f c = ∑ p ∈ n.primeFactors, ∑ j ∈ Icc 2 (n.factorization p), f (p, j)

**Theorem 1.3 (higherMass eq coordinate sum).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.higherMass_eq_coordinate_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.higherMass_eq_coordinate_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem higherMass_eq_coordinate_sum (n : ℕ) : higherMass n = ∑ c ∈ coordinates n, log (c.1 : ℝ)

**Theorem 1.4 (canonical mem).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.canonical_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.canonical_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem canonical_mem {η : ℝ} (hη : 0 < η) {p j : ℕ} : (p, j) ∈ coordinates (strictInteger η) ↔ p.Prime ∧ 2 ≤ j ∧ η < goldenLayerMarginal p j

**Theorem 1.5 (canonical coordinates antitone).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.canonical_coordinates_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.canonical_coordinates_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem canonical_coordinates_antitone {η ζ : ℝ} (hη : 0 < η) (hζ : 0 < ζ) (hηζ : η ≤ ζ) : coordinates (strictInteger ζ) ⊆ coordinates (strictInteger η)

**Theorem 1.6 (positive coordinate).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.positive_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.positive_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem positive_coordinate {η : ℝ} {p j : ℕ} (hp : p.Prime) : 0 < coordinateGain (p, j) - η * coordinateWeight (p, j) ↔ η < goldenLayerMarginal p j

**Theorem 1.7 (strictMass eq).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.strictMass_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.strictMass_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem strictMass_eq {η : ℝ} (hη : 0 < η) {S : Finset (ℕ × ℕ)} (hprime : ∀ c ∈ S, c.1.Prime ∧ 2 ≤ c.2) (hsub : coordinates (strictInteger η) ⊆ S) : strictMass S η = higherMass (strictInteger η)

**Theorem 1.8 (complete loss coordinates).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.complete_loss_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.complete_loss_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem complete_loss_coordinates {X : ℝ} (hX : 1 < X) (n : ℕ) : (∑ c ∈ coordinates (strictInteger (referencePrice X)) ∪ coordinates n, layerLoss X n c.1 c.2) = completeSecondLayerLoss X n + completeHigherLayerLoss X n

**Theorem 1.9 (literal loss identity).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.literal_loss_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.literal_loss_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem literal_loss_identity {X : ℝ} (hX : 1 < X) {n : ℕ} (hn : 1 ≤ n) (S : Finset (ℕ × ℕ)) (hprime : ∀ c ∈ S, c.1.Prime ∧ 2 ≤ c.2) (hsub : coordinates (strictInteger (referencePrice X)) ∪ coordinates n ⊆ S) : actualDefect X n - completeFirstLayerLoss X n = potential S (referencePrice X) - inventoryGain n + referencePrice X * higherMass n

**Theorem 1.10 (finite dual abs).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.finite_dual_abs`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.finite_dual_abs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem finite_dual_abs {ι : Type*} (S : Finset ι) (b w : ι → ℝ) (i : ι → Bool) (hw : ∀ c ∈ S, 0 ≤ w c) {«λ» t : ℝ} (ht : 0 < t) : let F := fun η => ∑ c ∈ S, max (b c - η * w c) 0 let h := fun η => ∑ c ∈ S, if 0 < b c - η * w c then w c else 0 let H := ∑ c ∈ S, if i c then w c else 0 let B := ∑ c ∈ S, if i c then b c else 0 let R := F «λ» - B + «λ» * H |H - h «λ»| ≤ R / t + h («λ» - t) - h («λ» + t)

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.canonical_coordinates_antitone`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.canonical_mem`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.complete_loss_coordinates`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.finite_dual_abs`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.higherMass_eq_coordinate_sum`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.literal_loss_identity`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.mem_coordinates`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.positive_coordinate`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.strictMass_eq`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.sum_coordinates`
- Dependency: [D5/S3/Arith/Robin/ActualTwoPriceDefect](../ActualTwoPriceDefect.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualRecordHigherLayerResidual](ActualRecordHigherLayerResidual.md)
