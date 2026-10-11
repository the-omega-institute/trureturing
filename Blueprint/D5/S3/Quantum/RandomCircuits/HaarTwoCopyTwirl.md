# The two-copy Haar moment and its local rule

## Abstract

The normalized two-copy Haar average is Hermitian and idempotent. Its action on two-site identity/swap vectors has coefficient q/(q squared + 1).

**Definition 1.1 (Compact unitary matrices).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \operatorname{CompactSpace}\left(\operatorname{Matrix.unitaryGroup}\left(n, \mathbb{C}\right)\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.unitaryCompactSpace` (`✓ std3`).

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

The unitary group is closed, and every matrix entry has norm at most one, so the finite-dimensional group is compact.

**Definition 1.2 (The Borel measurable structure).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \operatorname{unitaryMeasurableSpace}\left(n\right) = \operatorname{borel}\left(\operatorname{Matrix.unitaryGroup}\left(n, \mathbb{C}\right)\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.unitaryMeasurableSpace` (`✓ std3`).

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

The measurable sets are the Borel sets of the topology on unitary matrices.

**Definition 1.3 (Compatibility with the topology).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \operatorname{BorelSpace}\left(\operatorname{Matrix.unitaryGroup}\left(n, \mathbb{C}\right)\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.unitaryBorelSpace` (`✓ std3`).

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

The measurable structure is the Borel structure by definition.

**Definition 1.4 (Normalized Haar law).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \operatorname{IsProbabilityMeasure}\left(\operatorname{Measure.haarMeasure}\left((\operatorname{Top.top}: \operatorname{TopologicalSpace.PositiveCompacts}\left(\operatorname{Matrix.unitaryGroup}\left(n, \mathbb{C}\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.haar_probability` (`✓ std3`).

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

The compact Haar construction is normalized on the whole group. The top element of PositiveCompacts is the whole compact unitary group.

**Definition 1.5 (The literal four-replica action).**

$$\forall n \in Type,\; \forall U \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{literalMoment}\left(U\right) = \operatorname{Matrix.kronecker}\left(\operatorname{Matrix.kronecker}\left(\operatorname{Matrix.map}\left(U, star\right), \operatorname{Matrix.map}\left(U, star\right)\right), \operatorname{Matrix.kronecker}\left(U, U\right)\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.literalMoment` (`✓ std3`).

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

Section 2.1 (page 3) writes vec(Phi_epsilon) = E[U* tensor U* tensor U tensor U]. Here Matrix.map star is entrywise conjugation. The factors are barred replica one, barred replica two, unbarred replica one, unbarred replica two; Matrix.vec stacks columns first.

**Definition 1.6 (The Haar expectation).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall r \in ((n \times n) \times (n \times n)),\; \forall c \in ((n \times n) \times (n \times n)),\; \operatorname{haarAverage}\left(n\right)\left(r, c\right) = \int_{U: \operatorname{Matrix.unitaryGroup}\left(n, \mathbb{C}\right)} (\operatorname{literalMoment}\left(\operatorname{val}\left(U\right)\right)\left(r, c\right)) d(\operatorname{Measure.haarMeasure}\left((\operatorname{Top.top}: \operatorname{TopologicalSpace.PositiveCompacts}\left(\operatorname{Matrix.unitaryGroup}\left(n, \mathbb{C}\right)\right))\right))$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.haarAverage` (`✓ std3`).

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

The expectation is the entrywise Bochner integral of the literal four-factor action under normalized Haar law, not a projection substituted into the definition.

**Definition 1.7 (One-site permutation vectors).**

$$\forall q \in \mathbb{N},\; \forall b \in \operatorname{Fin}\left(2\right),\; \forall r \in ((\operatorname{Fin}\left(q\right) \times \operatorname{Fin}\left(q\right)) \times (\operatorname{Fin}\left(q\right) \times \operatorname{Fin}\left(q\right))),\; \operatorname{sitePermutation}\left(q, b, r\right) = \operatorname{ite}\left(b = 0, \operatorname{ite}\left((r.1.1 = r.2.1) \land (r.1.2 = r.2.2), ((q: \mathbb{C}))^{-1}, 0\right), \operatorname{ite}\left((r.1.1 = r.2.2) \land (r.1.2 = r.2.1), ((q: \mathbb{C}))^{-1}, 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.sitePermutation` (`✓ std3`).

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

The normalized identity vector pairs barred replica one with unbarred replica one, and likewise for replica two. The swap vector crosses those pairings. Their norm is one for positive local dimension.

**Definition 1.8 (Two-site permutation vectors).**

$$\forall q \in \mathbb{N},\; \forall b \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)),\; \forall r \in (((\operatorname{Fin}\left(q\right) \times \operatorname{Fin}\left(q\right)) \times (\operatorname{Fin}\left(q\right) \times \operatorname{Fin}\left(q\right))) \times ((\operatorname{Fin}\left(q\right) \times \operatorname{Fin}\left(q\right)) \times (\operatorname{Fin}\left(q\right) \times \operatorname{Fin}\left(q\right)))),\; \operatorname{localPermutation}\left(q, b\right)\left(r\right) = \operatorname{sitePermutation}\left(q, b.1, ((r.1.1.1, r.1.2.1), (r.2.1.1, r.2.2.1))\right) \cdot \operatorname{sitePermutation}\left(q, b.2, ((r.1.1.2, r.1.2.2), (r.2.1.2, r.2.2.2))\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.localPermutation` (`✓ std3`).

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

On the two sites of a gate the one-site identity or swap vector is chosen independently on each site. The matrix indices retain the original four-replica order.

**Theorem 1.9 (Haar averaging is Hermitian).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \operatorname{Matrix.IsHermitian}\left(\operatorname{haarAverage}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.haarAverage_hermitian` (`✓ std3`). ∎

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

Inversion preserves normalized Haar law, and the four-factor action of the inverse is the conjugate transpose of the original action.

**Theorem 1.10 (Haar averaging is idempotent).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \operatorname{haarAverage}\left(n\right) \cdot \operatorname{haarAverage}\left(n\right) = \operatorname{haarAverage}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.haarAverage_idempotent` (`✓ std3`). ∎

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

Left invariance fixes the averaged action under every unitary action, hence a second Haar average leaves it fixed.

**Theorem 1.11 (The physical two-site Gram matrix).**

$$\forall q \in \mathbb{N},\; (0 < q) \Rightarrow (\forall b \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)),\; \forall c \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)),\; \operatorname{dotProduct}\left(\operatorname{star}\left(\operatorname{localPermutation}\left(q, b\right)\right), \operatorname{localPermutation}\left(q, c\right)\right) = \operatorname{ite}\left(b.1 = c.1, 1, ((q: \mathbb{C}))^{-1}\right) \cdot \operatorname{ite}\left(b.2 = c.2, 1, ((q: \mathbb{C}))^{-1}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.localPermutation_gram` (`✓ std3`). ∎

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

The one-site overlap of equal identity/swap choices is one; distinct choices have overlap 1/q. The two-site overlap is the product of the two one-site overlaps.

**Theorem 1.12 (The identity vector is fixed).**

$$\forall q \in \mathbb{N},\; \operatorname{Matrix.mulVec}\left(\operatorname{haarAverage}\left((\operatorname{Fin}\left(q\right) \times \operatorname{Fin}\left(q\right))\right), \operatorname{localPermutation}\left(q, (0, 0)\right)\right) = \operatorname{localPermutation}\left(q, (0, 0)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.local_identity_fixed` (`✓ std3`). ∎

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

The identity commutes with the two-copy unitary action, so the Haar expectation fixes it.

**Theorem 1.13 (The swap vector is fixed).**

$$\forall q \in \mathbb{N},\; \operatorname{Matrix.mulVec}\left(\operatorname{haarAverage}\left((\operatorname{Fin}\left(q\right) \times \operatorname{Fin}\left(q\right))\right), \operatorname{localPermutation}\left(q, (1, 1)\right)\right) = \operatorname{localPermutation}\left(q, (1, 1)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.local_swap_fixed` (`✓ std3`). ∎

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

The replica swap commutes with the two-copy unitary action, so the Haar expectation fixes it.

**Theorem 1.14 (The exact mixed local rule).**

$$\forall q \in \mathbb{N},\; (2 \le q) \Rightarrow (\forall b \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)),\; (b.1 \ne b.2) \Rightarrow (\operatorname{Matrix.mulVec}\left(\operatorname{haarAverage}\left((\operatorname{Fin}\left(q\right) \times \operatorname{Fin}\left(q\right))\right), \operatorname{localPermutation}\left(q, b\right)\right) = (\frac{(q: \mathbb{C})}{(q: \mathbb{C})^{2} + 1}) \cdot (\operatorname{localPermutation}\left(q, (0, 0)\right) + \operatorname{localPermutation}\left(q, (1, 1)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.gate_mixed_rule` (`✓ std3`). ∎

*Citation.* Daniel Belkin, James Allen, Bryan K. Clark (2025). *Apparent Universal Behavior in 2nd Moments of Random Quantum Circuits*. URL: <https://arxiv.org/abs/2510.23726v2>.

*Commentary.*

Quarter phases force the two-copy commutant to have only identity and swap support. Permutations make its coefficients uniform; a two-coordinate Hadamard forces the remaining diagonal coefficient to be their sum. Haar invariance puts the image in this span. Hermitian pairing with the two fixed vectors then yields q/(q squared + 1) for each mixed input.

## References

- Truth anchor: `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.gate_mixed_rule`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.haarAverage`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.haarAverage_hermitian`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.haarAverage_idempotent`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.haar_probability`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.literalMoment`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.localPermutation`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.localPermutation_gram`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.local_identity_fixed`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.local_swap_fixed`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.sitePermutation`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.unitaryBorelSpace`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.unitaryCompactSpace`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.unitaryMeasurableSpace`
