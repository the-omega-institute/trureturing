# PowerCompactness

## Abstract

Algebraic width turns a verbal subgroup into a closed compact image.

**Definition 1.1 (Ordered products of powers).**

$$\operatorname{powerProduct}(m, w, a) = \operatorname{OrderedProduct}(\operatorname{Fin}(w), i \mapsto \operatorname{a}(i)^{m})$$

*Formalization.* `D5/S3/Factorization/Galois/PowerCompactness.powerProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product follows the order on Fin w. It contains exactly w factors of the form a(i) to the mth power. An empty product is one; factors are never permuted.

**Definition 1.2 (Algebraic power width).**

$$\operatorname{HasPowerWidth}(G, m, w) \iff \forall (g: G), {g \in \operatorname{powerSubgroup}(G, m)} \Rightarrow {\exists (a: \operatorname{Functions}(\operatorname{Fin}(w), G)), \operatorname{powerProduct}(m, w, a) = g}$$

*Formalization.* `D5/S3/Factorization/Galois/PowerCompactness.HasPowerWidth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every element of the generated power subgroup must be represented by an ordered product of exactly w powers. Padding uses identity elements. This is an algebraic proposition, with no openness assumption.

**Theorem 1.3 (Product membership).**

$$\forall (a: \operatorname{Functions}(\operatorname{Fin}(w), G)), \operatorname{powerProduct}(m, w, a) \in \operatorname{powerSubgroup}(G, m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/PowerCompactness.powerProduct_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An ordered product of powers belongs to their generated subgroup in any group, including width zero.

**Theorem 1.4 (The power-product image).**

$${\operatorname{HasPowerWidth}(G, m, w)} \Rightarrow {\operatorname{Range}(\operatorname{powerProduct}(m, w)) = \operatorname{powerSubgroup}(G, m)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/PowerCompactness.range_powerProduct_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the width proposition, the power subgroup equals the image of the ordered product map.

**Theorem 1.5 (Continuity of ordered products).**

$${\operatorname{TopologicalGroup}(G)} \Rightarrow {\operatorname{Continuous}(\operatorname{powerProduct}(m, w))}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/PowerCompactness.continuous_powerProduct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a topological group the finite ordered product of coordinatewise powers is continuous.

**Theorem 1.6 (Compact image gives closedness).**

$${\operatorname{CompactHausdorffTopologicalGroup}(G)} \Rightarrow {{\operatorname{HasPowerWidth}(G, m, w)} \Rightarrow {\operatorname{IsClosed}(\operatorname{powerSubgroup}(G, m))}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/PowerCompactness.isClosed_powerSubgroup_of_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a compact Hausdorff topological group, bounded algebraic width makes the power subgroup a compact finite-product image and hence a closed set.

**Theorem 1.7 (Closed finite quotient gives openness).**

$${\operatorname{TopologicalGroup}(G)} \Rightarrow {{\operatorname{IsClosed}(\operatorname{powerSubgroup}(G, m)) \land \operatorname{Finite}(\operatorname{Quotient}(G, \operatorname{powerSubgroup}(G, m)))} \Rightarrow {\operatorname{IsOpen}(\operatorname{powerSubgroup}(G, m))}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/PowerCompactness.isOpen_powerSubgroup_of_closed_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a topological group, a closed power subgroup with an explicitly finite abstract quotient is open, by the closed finite-index subgroup theorem.

## References

- Truth anchor: `D5/S3/Factorization/Galois/PowerCompactness.HasPowerWidth`
- Truth anchor: `D5/S3/Factorization/Galois/PowerCompactness.continuous_powerProduct`
- Truth anchor: `D5/S3/Factorization/Galois/PowerCompactness.isClosed_powerSubgroup_of_width`
- Truth anchor: `D5/S3/Factorization/Galois/PowerCompactness.isOpen_powerSubgroup_of_closed_finite`
- Truth anchor: `D5/S3/Factorization/Galois/PowerCompactness.powerProduct`
- Truth anchor: `D5/S3/Factorization/Galois/PowerCompactness.powerProduct_mem`
- Truth anchor: `D5/S3/Factorization/Galois/PowerCompactness.range_powerProduct_eq`
- Dependency: [D5/S3/Factorization/Galois/NormalCorePower](NormalCorePower.md)
