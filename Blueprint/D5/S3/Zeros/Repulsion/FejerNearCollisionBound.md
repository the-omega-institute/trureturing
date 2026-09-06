# Signed-Mode Fejer Near-Collision Bounds

## Abstract

Signed-mode Fejer kernels give finite Fourier identities and collision bounds.

All quotients displayed with M occur in the real numbers after coercing M. The symbol g denotes the same finite real family in every binder and body.

**Definition 1.1 (The kernel is the signed integer-mode cosine sum).**

$$\forall M \in \mathbb{N}, t \in \mathbb{R},\; \left(F_{M}\right)\left(t\right) = \sum_{k \in \mathbb{Z} \land \left|k\right| < \operatorname{val}\left(M\right)_{\mathbb{Z}}} (1 - \frac{\operatorname{val}\left(\left|k\right|\right)_{\mathbb{R}}}{\operatorname{val}\left(M\right)_{\mathbb{R}}}) \cdot \operatorname{cos}\left(\operatorname{val}\left(k\right)_{\mathbb{R}} \cdot t\right)$$

*Formalization.* `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.fejerKernel` (`✓ std3`).

*Citation.* Leopold Fejer (1903). *Untersuchungen uber Fouriersche Reihen*. DOI: [10.1007/BF01447779](https://doi.org/10.1007/BF01447779).

*Commentary.*

For natural M and real t, F_M(t) is the sum over every integer k with |k| < M of (1-|k|/M) cos(kt). This is the defining expression, not an abbreviation for a paired nonnegative-mode polynomial.

**Definition 1.2 (Energy is the ordered double kernel sum).**

$$\forall n \in \mathbb{N}, M \in \mathbb{N}, g \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \operatorname{fejerEnergy}\left(M, g\right) = \sum_{i \in \operatorname{Fin}\left(n\right)} \sum_{j \in \operatorname{Fin}\left(n\right)} (\sum_{k \in \mathbb{Z} \land \left|k\right| < \operatorname{val}\left(M\right)_{\mathbb{Z}}} (1 - \frac{\operatorname{val}\left(\left|k\right|\right)_{\mathbb{R}}}{\operatorname{val}\left(M\right)_{\mathbb{R}}}) \cdot \operatorname{cos}\left(\operatorname{val}\left(k\right)_{\mathbb{R}} \cdot \left(g_{i} - g_{j}\right)\right))$$

*Formalization.* `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.fejerEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For g : Fin n -> R, fejerEnergy M g is the ordered sum of F_M(g_i-g_j) over all i and j in Fin n.

**Definition 1.3 (Near-pair count is a filtered ordered-pair cardinality).**

$$\forall n \in \mathbb{N}, M \in \mathbb{N}, g \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \operatorname{nearPairCount}\left(M, g\right) = \lvert\left\{(i, j) \in \operatorname{Fin}\left(n\right)^{2} \mid \left|g_{i} - g_{j}\right| \le \frac{\pi}{\operatorname{val}\left(M\right)_{\mathbb{R}}}\right\}\rvert$$

*Formalization.* `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.nearPairCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

nearPairCount M g is the natural-number cardinality of ordered pairs (i,j) in Fin n squared whose values differ by at most pi/M.

**Theorem 1.4 (The signed-mode kernel is a normalized square).**

$$\forall M \in \mathbb{N}, t \in \mathbb{R},\; 1 \le M \Rightarrow \sum_{k \in \mathbb{Z} \land \left|k\right| < \operatorname{val}\left(M\right)_{\mathbb{Z}}} (1 - \frac{\operatorname{val}\left(\left|k\right|\right)_{\mathbb{R}}}{\operatorname{val}\left(M\right)_{\mathbb{R}}}) \cdot \operatorname{cos}\left(\operatorname{val}\left(k\right)_{\mathbb{R}} \cdot t\right) = \frac{1}{\operatorname{val}\left(M\right)_{\mathbb{R}}} \cdot \left\lVert \sum_{0 \le r \land r < M} \operatorname{exp}\left(\operatorname{val}\left(\operatorname{val}\left(r\right)_{\mathbb{R}} \cdot t\right)_{\mathbb{C}} \cdot \mathrm{i}\right) \right\rVert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.fejer_square` (`✓ std3`). ∎

*Citation.* Leopold Fejer (1903). *Untersuchungen uber Fouriersche Reihen*. DOI: [10.1007/BF01447779](https://doi.org/10.1007/BF01447779).

*Commentary.*

For every positive natural M and real t, the atom-defined signed-mode kernel equals one over M times the squared norm of the length-M geometric exponential sum.

A private pairing lemma partitions the signed modes into zero, positive, and negative parts. The square identity is then proved by induction on the geometric-sum length.

**Theorem 1.5 (Ordered kernel energy equals signed Fourier energy).**

$$\forall n \in \mathbb{N}, M \in \mathbb{N}, g \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \sum_{i \in \operatorname{Fin}\left(n\right)} \sum_{j \in \operatorname{Fin}\left(n\right)} (\sum_{k \in \mathbb{Z} \land \left|k\right| < \operatorname{val}\left(M\right)_{\mathbb{Z}}} (1 - \frac{\operatorname{val}\left(\left|k\right|\right)_{\mathbb{R}}}{\operatorname{val}\left(M\right)_{\mathbb{R}}}) \cdot \operatorname{cos}\left(\operatorname{val}\left(k\right)_{\mathbb{R}} \cdot \left(g_{i} - g_{j}\right)\right)) = \sum_{k \in \mathbb{Z} \land \left|k\right| < \operatorname{val}\left(M\right)_{\mathbb{Z}}} (1 - \frac{\operatorname{val}\left(\left|k\right|\right)_{\mathbb{R}}}{\operatorname{val}\left(M\right)_{\mathbb{R}}}) \cdot \left\lVert \sum_{i \in \operatorname{Fin}\left(n\right)} \operatorname{exp}\left(\operatorname{val}\left(\operatorname{val}\left(k\right)_{\mathbb{R}} \cdot g_{i}\right)_{\mathbb{C}} \cdot \mathrm{i}\right) \right\rVert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.fejer_energy_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordered double sum of the atom-defined kernel equals the signed mode sum of weighted squared exponential-sum norms. The proof swaps the finite sums and turns each cosine pair sum into a complex norm square.

Named companion: fejer_energy_identity discharges the finite signed Fourier-energy identity obligation, atom 24.92 (ef059c215ec75472aa55d6d4b9c8fde6c5e8321ed941c9f51987d4402d8fa28f). preregistered named use: atom 24.92 obligation (评注 24.9x 预登记). The registration artifact is the candidate theorem 24.92 and remark 27.799 in the PZG reference source. No public theorem in this module consumes fejer_energy_identity in its proof graph.

**Theorem 1.6 (The signed-mode kernel is large on its central window).**

$$\forall M \in \mathbb{N}, t \in \mathbb{R},\; \left(1 \le M \land \left|t\right| \le \frac{\pi}{\operatorname{val}\left(M\right)_{\mathbb{R}}}\right) \Rightarrow \frac{4 \cdot \operatorname{val}\left(M\right)_{\mathbb{R}}}{\pi^{2}} \le \sum_{k \in \mathbb{Z} \land \left|k\right| < \operatorname{val}\left(M\right)_{\mathbb{Z}}} (1 - \frac{\operatorname{val}\left(\left|k\right|\right)_{\mathbb{R}}}{\operatorname{val}\left(M\right)_{\mathbb{R}}}) \cdot \operatorname{cos}\left(\operatorname{val}\left(k\right)_{\mathbb{R}} \cdot t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.fejer_local_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If M is positive and |t| <= pi/M, the atom-defined signed-mode kernel is at least 4M/pi^2.

**Theorem 1.7 (Signed-mode energy controls ordered near collisions).**

$$\forall n \in \mathbb{N}, M \in \mathbb{N}, g \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; 1 \le M \Rightarrow \operatorname{val}\left(\lvert\left\{(i, j) \in \operatorname{Fin}\left(n\right)^{2} \mid \left|g_{i} - g_{j}\right| \le \frac{\pi}{\operatorname{val}\left(M\right)_{\mathbb{R}}}\right\}\rvert\right)_{\mathbb{R}} \le \frac{\pi^{2}}{4 \cdot \operatorname{val}\left(M\right)_{\mathbb{R}}} \cdot \sum_{i \in \operatorname{Fin}\left(n\right)} \sum_{j \in \operatorname{Fin}\left(n\right)} (\sum_{k \in \mathbb{Z} \land \left|k\right| < \operatorname{val}\left(M\right)_{\mathbb{Z}}} (1 - \frac{\operatorname{val}\left(\left|k\right|\right)_{\mathbb{R}}}{\operatorname{val}\left(M\right)_{\mathbb{R}}}) \cdot \operatorname{cos}\left(\operatorname{val}\left(k\right)_{\mathbb{R}} \cdot \left(g_{i} - g_{j}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.near_pair_count_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real coercion of the filtered ordered-pair cardinality is bounded by pi^2/(4M) times the displayed ordered double kernel sum. The proof uses the local lower bound on near pairs and square nonnegativity elsewhere.

**Theorem 1.8 (Signed-mode energy dominates squared multiplicities).**

$$\forall n \in \mathbb{N}, M \in \mathbb{N}, g \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; 1 \le M \Rightarrow \operatorname{val}\left(M\right)_{\mathbb{R}} \cdot \sum_{v \in \operatorname{im}\left(g\right)} \left(\operatorname{val}\left(\lvert\left\{i \in \operatorname{Fin}\left(n\right) \mid g_{i} = v\right\}\rvert\right)_{\mathbb{R}}\right)^{2} \le \sum_{i \in \operatorname{Fin}\left(n\right)} \sum_{j \in \operatorname{Fin}\left(n\right)} (\sum_{k \in \mathbb{Z} \land \left|k\right| < \operatorname{val}\left(M\right)_{\mathbb{Z}}} (1 - \frac{\operatorname{val}\left(\left|k\right|\right)_{\mathbb{R}}}{\operatorname{val}\left(M\right)_{\mathbb{R}}}) \cdot \operatorname{cos}\left(\operatorname{val}\left(k\right)_{\mathbb{R}} \cdot \left(g_{i} - g_{j}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.distinct_multiplicity_energy_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed ordered double kernel sum is at least M times the sum, over values attained by g, of the squared real-coerced fiber cardinality.

This finite inequality supplies no zeta-zero asymptotic and no positive proportion of simple zeros without an independent energy upper bound.

## References

- Truth anchor: `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.distinct_multiplicity_energy_lower_bound`
- Truth anchor: `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.fejerEnergy`
- Truth anchor: `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.fejerKernel`
- Truth anchor: `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.fejer_energy_identity`
- Truth anchor: `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.fejer_local_lower_bound`
- Truth anchor: `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.fejer_square`
- Truth anchor: `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.nearPairCount`
- Truth anchor: `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.near_pair_count_bound`
