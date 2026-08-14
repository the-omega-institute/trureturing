# Collision Entropy versus Shannon Entropy

## Abstract

The order-two collision expression is bounded by Shannon entropy, with equality exactly at laws uniform on their positive support.

The frozen CollisionEntropyUncertainty proof already contained this comparison as an internal have: each measurement law has Shannon entropy at least minus the logarithm of its squared-mass sum. That local fact was unavailable outside the enclosing proof. The present module re-establishes the Jensen argument as a top-level theorem and adds its equality characterization.

The equality condition is pairwise equality on positive support, not uniformity over every index. A point mass on a carrier with at least two indices attains equality: its squared-mass sum is one and H is zero, but it is not uniform across the full carrier. A full-index uniformity biconditional would therefore be false. The theorem name collision_entropy_eq_shannon_entropy_iff_uniform_on_support records the exact condition, whereas collision_entropy_eq_shannon_entropy_of_uniform states full-index uniformity only as a sufficient condition.

The proof replaces every zero mass by the positive logarithm argument one and then applies weighted logarithmic Jensen. Strict concavity identifies equality only among coordinates carrying nonzero weight, which is precisely the positive support because the law is nonnegative. Normalization rules out an empty carrier, so no separate nonemptiness assumption is required.

This module treats only the order-two collision expression -log(SUM p(i)^2). It does not state general Renyi-entropy monotonicity.

All three displays are authored legally because the current statement projector has no pinned projectable fixture for these declarations. Document construction therefore records a ProjectionGap for each theorem.

**Theorem 1.1 (Order-two collision entropy is at most Shannon entropy).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p: \iota\to \mathbb{R},\\((\forall i, 0 \le p(i)) \land\\\sum _{i} p(i) = 1) \Rightarrow\\-\log (\sum _{i} p(i)^{2}) \le H(p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CollisionShannonComparison.collision_entropy_le_shannon_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite nonnegative law of total mass one, the theorem exports the comparison that was previously confined to the uncertainty proof. The zero-mass substitution contributes neither to the weighted logarithmic sum nor to the squared-mass sum, while making every logarithm argument strictly positive. Negating the resulting concave Jensen inequality gives the displayed lower bound for H.

**Theorem 1.2 (Collision-Shannon equality is uniformity on positive support).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p: \iota\to \mathbb{R},\\((\forall i, 0 \le p(i)) \land\\\sum _{i} p(i) = 1) \Rightarrow\\(-\log (\sum _{i} p(i)^{2}) = H(p)) \Leftrightarrow\\\forall i j, 0 < p(i) \Rightarrow 0 < p(j) \Rightarrow p(i) = p(j).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CollisionShannonComparison.collision_entropy_eq_shannon_entropy_iff_uniform_on_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of the two entropy expressions is rewritten as equality in the weighted logarithmic Jensen step. The strict-concavity equality criterion then equates the substituted logarithm arguments exactly where their weights are nonzero. Nonnegativity converts nonzero mass into positive mass, yielding pairwise equality on positive support in both directions without imposing any condition on zero coordinates.

**Theorem 1.3 (Full-index uniformity suffices for Collision-Shannon equality).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p: \iota\to \mathbb{R},\\((\forall i, 0 \le p(i)) \land\\\sum _{i} p(i) = 1) \Rightarrow\\(\forall i j, p(i) = p(j)) \Rightarrow\\-\log (\sum _{i} p(i)^{2}) = H(p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CollisionShannonComparison.collision_entropy_eq_shannon_entropy_of_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Uniformity on the entire finite index type immediately supplies pairwise equality on positive support. The sufficient theorem applies the reverse direction of the preceding biconditional. Its one-way form is essential: zero coordinates prevent full-index uniformity from being necessary.

## References

- Truth anchor: `D5/S3/QuantumBounds/CollisionShannonComparison.collision_entropy_eq_shannon_entropy_iff_uniform_on_support`
- Truth anchor: `D5/S3/QuantumBounds/CollisionShannonComparison.collision_entropy_eq_shannon_entropy_of_uniform`
- Truth anchor: `D5/S3/QuantumBounds/CollisionShannonComparison.collision_entropy_le_shannon_entropy`
- Dependency: [D5/S3/Entropy/MaxEntropy](../Entropy/MaxEntropy.md)
