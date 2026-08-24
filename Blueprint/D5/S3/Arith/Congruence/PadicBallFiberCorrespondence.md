# Prime-Power Congruence Fibers as P-Adic Balls

## Abstract

A prime-power congruence class is the integer trace of a p-adic closed ball.

**Lemma 1.1 (Prime-power congruence is exactly p-adic proximity).**

$$\forall p, k \in \mathbb{N}, p \text{ prime}, x, y \in \mathbb{Z},\ x \equiv y (\operatorname{mod} p^{k}) \iff d_{p}(x, y) \leq p^{-k}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/PadicBallFiberCorrespondence.modeq_iff_padic_dist_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p and a precision k, two integers occupy the same residue class modulo p^k exactly when their images in the p-adic numbers are at distance at most p^(-k). Thus arithmetic agreement through k p-adic digits is the same condition as metric proximity at the corresponding scale.

The distance between the embedded integers is the p-adic norm of their difference. Divisibility of that difference by p^k is equivalent to its norm being bounded by p^(-k), which converts the congruence condition into the stated distance bound in both directions.

**Theorem 1.2 (A congruence fiber is the integer trace of a closed ball).**

$$\forall p, k \in \mathbb{N}, p \text{ prime}, x \in \mathbb{Z},\ \operatorname{congruenceFiber}\left(p, k, x\right) = \{ z \in \mathbb{Q}_{p} \mid d_{p}(x, z) \leq p^{-k} \land z \in iota_{p}(\mathbb{Z}) \}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/PadicBallFiberCorrespondence.congruenceFiber_eq_closedBall_inter_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p, precision k, and integer center x, the p-adic images of integers congruent to x modulo p^k are precisely the points in the closed ball of radius p^(-k) around x that also lie in the embedded copy of the integers. The integer-image restriction is essential: the ambient p-adic ball contains points that do not arise from integers.

Membership in the congruence fiber supplies an integer representative y. The distance characterization turns x congruent to y modulo p^k into the closed-ball inequality, while the embedding of y supplies membership in the integer image. Conversely, an integer point of the ball has a representative y, and the same characterization recovers its congruence to x, giving both inclusions of the set equality.

## References

- Truth anchor: `D5/S3/Arith/Congruence/PadicBallFiberCorrespondence.congruenceFiber_eq_closedBall_inter_range`
- Truth anchor: `D5/S3/Arith/Congruence/PadicBallFiberCorrespondence.modeq_iff_padic_dist_le`
