# Collisions of integer plastic powers

## Abstract

Integer plastic powers have four collision templates, disjoint unordered-pair fibers, and an exact finite-subset sumset identity.

Throughout, r is a real number with r > 1 and r³ = r + 1. Every exponent is an integer. For a finite integer set E, A(r,E) denotes its image under e ↦ rᵉ. A(r,E) + A(r,E) is the actual pointwise real sumset. Pairs are sorted, with repeated summands permitted. For d,a,b, N(E,d,a,b) is the cardinality of {t ∈ E : t+a ∈ E, t+b ∈ E, t+d ∈ E}. These are abbreviations for the explicit Finset.image and Finset.filter expressions in Lean, without an abstract sumset model.

**Theorem 1.1 (The integer difference equation).**

$$\forall (r : \mathbb{R}), (1 < r) \Rightarrow ((r^{3} = r + 1) \Rightarrow (\forall (u : \mathbb{Z}), \forall (v : \mathbb{Z}), (r^{u} - r^{v} = 1) \Leftrightarrow (((((u = 1) \land (v = -4)) \lor ((u = 2) \land (v = -1))) \lor ((u = 3) \land (v = 1))) \lor ((u = 5) \land (v = 4)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/PlasticPowerCollisions.difference_eq_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Attila Bérczes (2010). *On the sumset of geometric progressions*. DOI: [10.5486/PMD.2010.4683](https://doi.org/10.5486/PMD.2010.4683). URL: <https://doi.org/10.5486/PMD.2010.4683>.

*Commentary.*

If the lower exponent is negative, the upper exponent lies strictly between zero and three. Otherwise dividing by the lower power bounds the positive exponent gap by two. The identities r−1 = r⁻⁴ and r²−1 = r⁻¹ give all four solutions. This elementary argument is the source proof's intermediate step; negative exponents remain in its domain.

**Theorem 1.2 (All four normalized templates).**

$$\forall (r : \mathbb{R}), (1 < r) \Rightarrow ((r^{3} = r + 1) \Rightarrow (\forall (d : \mathbb{Z}), \forall (a : \mathbb{Z}), \forall (b : \mathbb{Z}), (1 \le a) \Rightarrow ((a \le b) \Rightarrow ((b < d) \Rightarrow ((1 + r^{d} = r^{a} + r^{b}) \Leftrightarrow (((((d = 4) \land ((a = 2) \land (b = 3))) \lor ((d = 6) \land ((a = 3) \land (b = 5)))) \lor ((d = 7) \land ((a = 5) \land (b = 5)))) \lor ((d = 9) \land ((a = 5) \land (b = 8)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/PlasticPowerCollisions.normalized_collision_iff` (`✓ std3`). ∎

*Citation.* Attila Bérczes (2010). *On the sumset of geometric progressions*. DOI: [10.5486/PMD.2010.4683](https://doi.org/10.5486/PMD.2010.4683). URL: <https://doi.org/10.5486/PMD.2010.4683>.

*Commentary.*

Dividing by the largest inner power shows that d−b is one or two, since the resulting power is below two and r³ > 2. The difference classification then gives exactly (4,2,3), (6,3,5), (7,5,5), and (9,5,8). The third template retains the diagonal pair. Bérczes Theorems 2.2 and 2.3 attest the collision classification.

**Theorem 1.3 (Translated sorted pairs).**

$$\forall (r : \mathbb{R}), (1 < r) \Rightarrow ((r^{3} = r + 1) \Rightarrow (\forall (i : \mathbb{Z}), \forall (j : \mathbb{Z}), \forall (k : \mathbb{Z}), \forall (l : \mathbb{Z}), (i \le j) \Rightarrow ((k \le l) \Rightarrow ((i < k) \Rightarrow ((r^{i} + r^{j} = r^{k} + r^{l}) \Leftrightarrow (((((j = i + 4) \land ((k = i + 2) \land (l = i + 3))) \lor ((j = i + 6) \land ((k = i + 3) \land (l = i + 5)))) \lor ((j = i + 7) \land ((k = i + 5) \land (l = i + 5)))) \lor ((j = i + 9) \land ((k = i + 5) \land (l = i + 8)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/PlasticPowerCollisions.sorted_collision_iff` (`✓ std3`). ∎

*Citation.* Attila Bérczes (2010). *On the sumset of geometric progressions*. DOI: [10.5486/PMD.2010.4683](https://doi.org/10.5486/PMD.2010.4683). URL: <https://doi.org/10.5486/PMD.2010.4683>.

*Commentary.*

For sorted pairs with i < k, an equality of sums forces l < j. Dividing by rⁱ converts to the normalized equation. The converse multiplies that equation by the same nonzero power, preserving all integer translates.

**Theorem 1.4 (Actual sum fibers have size at most two).**

$$\forall (r : \mathbb{R}), (1 < r) \Rightarrow ((r^{3} = r + 1) \Rightarrow (\forall (E : \operatorname{Finset}\left(\mathbb{Z}\right)), \forall (x : \mathbb{R}), \lvert \{p : \mathbb{Z} \times \mathbb{Z} \mid (p \in E \times E) \land ((p_{1} \le p_{2}) \land (r^{p_{1}} + r^{p_{2}} = x))\}\rvert  \le 2))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/PlasticPowerCollisions.sum_fiber_card_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Attila Bérczes (2010). *On the sumset of geometric progressions*. DOI: [10.5486/PMD.2010.4683](https://doi.org/10.5486/PMD.2010.4683). URL: <https://doi.org/10.5486/PMD.2010.4683>.

*Commentary.*

Pairs with the same first exponent and the same sum are equal. For three distinct representations, order the first exponents. The middle pair would need both an outer gap in {4,6,7,9} and an inner gap in {0,1,2,3}. These are disjoint, so three representations cannot occur.

**Theorem 1.5 (One representative for every real sum).**

$$\forall (r : \mathbb{R}), (1 < r) \Rightarrow ((r^{3} = r + 1) \Rightarrow (\forall (E : \operatorname{Finset}\left(\mathbb{Z}\right)), \lvert \operatorname{A}\left(r, E\right) + \operatorname{A}\left(r, E\right)\rvert  = \lvert \{p : \mathbb{Z} \times \mathbb{Z} \mid (p \in E \times E) \land ((p_{1} \le p_{2}) \land (\neg \operatorname{O}\left(E, p\right)))\}\rvert ))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/PlasticPowerCollisions.sumset_card_eq_reduced_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Attila Bérczes (2010). *On the sumset of geometric progressions*. DOI: [10.5486/PMD.2010.4683](https://doi.org/10.5486/PMD.2010.4683). URL: <https://doi.org/10.5486/PMD.2010.4683>.

*Commentary.*

Write O(E,p) for the disjunction p₂=p₁+4 with p₁+2,p₁+3 in E; p₂=p₁+6 with p₁+3,p₁+5 in E; p₂=p₁+7 with p₁+5 in E; or p₂=p₁+9 with p₁+5,p₁+8 in E. Each excluded outer pair has an inner partner in E with the same actual real sum. That partner cannot itself be outer, since this would give three representations. The sum map on the remaining pairs is both injective and onto the actual sumset.

**Theorem 1.6 (Exact counting for arbitrary finite exponent sets).**

$$\forall (r : \mathbb{R}), (1 < r) \Rightarrow ((r^{3} = r + 1) \Rightarrow (\forall (E : \operatorname{Finset}\left(\mathbb{Z}\right)), \lvert \operatorname{A}\left(r, E\right) + \operatorname{A}\left(r, E\right)\rvert  + \operatorname{N}\left(E, 4, 2, 3\right) + \operatorname{N}\left(E, 6, 3, 5\right) + \operatorname{N}\left(E, 7, 5, 5\right) + \operatorname{N}\left(E, 9, 5, 8\right) = \operatorname{choose}\left(\lvert E\rvert  + 1, 2\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/PlasticPowerCollisions.sumset_card_add_template_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Attila Bérczes (2010). *On the sumset of geometric progressions*. DOI: [10.5486/PMD.2010.4683](https://doi.org/10.5486/PMD.2010.4683). URL: <https://doi.org/10.5486/PMD.2010.4683>.

*Commentary.*

The excluded pairs form the disjoint union of the four translated templates; their outer gaps distinguish the four parts. Each part is in bijection with its starting exponents. All sorted pairs consist of the strictly ordered pairs and the diagonal, so their total is choose(|E|+1,2). The additive identity proves that subtracting the four counts cannot truncate. The three-point template uses N(E,7,5,5), where the repeated membership condition is redundant.

**Theorem 1.7 (The exact native nested-family sumset).**

$$\forall (r : \mathbb{R}), (1 < r) \Rightarrow ((r^{3} = r + 1) \Rightarrow (\forall (n : \mathbb{N}), (7 \le n) \Rightarrow (\lvert \operatorname{B}\left(r, n\right) + \operatorname{B}\left(r, n\right)\rvert  + n - 1 + (n - 8)_{+} + (n - 9)_{+} + (n - 11)_{+} + 1_{8 \le n} + 1_{10 \le n} = \frac{n \cdot (n + 1)}{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/PlasticPowerCollisions.nested_family_sum_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Attila Bérczes (2010). *On the sumset of geometric progressions*. DOI: [10.5486/PMD.2010.4683](https://doi.org/10.5486/PMD.2010.4683). URL: <https://doi.org/10.5486/PMD.2010.4683>.

*Commentary.*

Let E(n) = {0,3} ∪ [5,n+2] over the integers, and B(r,n) = A(r,E(n)). For n ≥ 7, this exponent set has n elements. The starting exponents for the four templates are respectively {3} ∪ [5,n−2], {0,3} ∪ [5,n−4], {0} together with 3 when n ≥ 8 and [5,n−5], and {0} together with 3 when n ≥ 10 and [5,n−7]. Counting these sets and applying the exact finite-subset identity gives every positive-part and indicator term in source Theorem 2.1. Natural subtraction represents the positive parts; the additive equality proves no truncation in the displayed source subtraction.

This supplies the collision and arbitrary-finite-subset counting bridge used in the proof of source Theorem 2.1. The source theorem additionally requires its product equality, strict nesting, and the comparison with the golden-ratio power set. Those additional claims are not consequences asserted by this document.

## References

- Truth anchor: `D5/S3/Arith/Additive/PlasticPowerCollisions.difference_eq_one_iff`
- Truth anchor: `D5/S3/Arith/Additive/PlasticPowerCollisions.nested_family_sum_card`
- Truth anchor: `D5/S3/Arith/Additive/PlasticPowerCollisions.normalized_collision_iff`
- Truth anchor: `D5/S3/Arith/Additive/PlasticPowerCollisions.sorted_collision_iff`
- Truth anchor: `D5/S3/Arith/Additive/PlasticPowerCollisions.sum_fiber_card_le_two`
- Truth anchor: `D5/S3/Arith/Additive/PlasticPowerCollisions.sumset_card_add_template_counts`
- Truth anchor: `D5/S3/Arith/Additive/PlasticPowerCollisions.sumset_card_eq_reduced_pairs`
