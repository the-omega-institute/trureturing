# The sharp upper endpoint of the Zhang–Jing power block

## Abstract

The power block characterizes normality for 1/2 ≤ a < 1, including singular matrices; at a = 1 it is positive semidefinite for every matrix.

**Definition 1.1 (The source's unresolved closed interval).**

$$(claim) \Leftrightarrow ((\forall (a: \mathbb{R}), (\frac{1}{2} \le a) \Rightarrow ((a \le 1) \Rightarrow (\forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix.PosSemidef}\left(\operatorname{D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation.block}\left((fun (x: \mathbb{R}) \mapsto x^{2 \cdot a}), (fun (x: \mathbb{R}) \mapsto x^{2 \cdot (1 - a)}), A\right)\right)) \Leftrightarrow (\operatorname{Matrix.conjTranspose}\left(A\right) \cdot A = A \cdot \operatorname{Matrix.conjTranspose}\left(A\right))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.claim` (`✓ std3`).

*Citation.* Feng Zhang; Hefang Jing (2025). *More inequalities for positive semidefinite matrices*. DOI: [10.13001/ela.2025.9201](https://doi.org/10.13001/ela.2025.9201). URL: <https://doi.org/10.13001/ela.2025.9201>.

*Commentary.*

After Remark 2.13, p. 601: “Due to the limitations of our research method, we cannot solve the problem that Theorem 2.3 holds for 1/2 ≤ a ≤ 1.” The proposition expands the equivalence over every real a in that interval, every natural dimension n, and every complex square matrix A. The matrix functions use Real.rpow, with x⁰ = 1. PosSemidef means positive semidefinite, and normality means Aᴴ A = A Aᴴ.

**Definition 1.2 (The interval below the upper endpoint).**

$$(claimBelowOne) \Leftrightarrow ((\forall (a: \mathbb{R}), (\frac{1}{2} \le a) \Rightarrow ((a < 1) \Rightarrow (\forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix.PosSemidef}\left(\operatorname{D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation.block}\left((fun (x: \mathbb{R}) \mapsto x^{2 \cdot a}), (fun (x: \mathbb{R}) \mapsto x^{2 \cdot (1 - a)}), A\right)\right)) \Leftrightarrow (\operatorname{Matrix.conjTranspose}\left(A\right) \cdot A = A \cdot \operatorname{Matrix.conjTranspose}\left(A\right))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.claimBelowOne` (`✓ std3`).

*Citation.* Feng Zhang; Hefang Jing (2025). *More inequalities for positive semidefinite matrices*. DOI: [10.13001/ela.2025.9201](https://doi.org/10.13001/ela.2025.9201). URL: <https://doi.org/10.13001/ela.2025.9201>.

*Commentary.*

The equivalence of Theorem 2.3 is restricted to 1/2 ≤ a < 1. Matrices may be singular, and dimension zero is included. This is the positive portion of the source's interval quoted after Remark 2.13 on p. 601.

**Theorem 1.3 (The extension to a = 1 fails).**

$$\neg (\forall (a: \mathbb{R}), (\frac{1}{2} \le a) \Rightarrow ((a \le 1) \Rightarrow (\forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix.PosSemidef}\left(\operatorname{D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation.block}\left((fun (x: \mathbb{R}) \mapsto x^{2 \cdot a}), (fun (x: \mathbb{R}) \mapsto x^{2 \cdot (1 - a)}), A\right)\right)) \Leftrightarrow (\operatorname{Matrix.conjTranspose}\left(A\right) \cdot A = A \cdot \operatorname{Matrix.conjTranspose}\left(A\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Feng Zhang; Hefang Jing (2025). *More inequalities for positive semidefinite matrices*. DOI: [10.13001/ela.2025.9201](https://doi.org/10.13001/ela.2025.9201). URL: <https://doi.org/10.13001/ela.2025.9201>.

*Commentary.*

At a = 1 the diagonal corners are Aᴴ A and I, so the block is Qᴴ Q for Q = [A,I], padded by zero rows to form a square matrix. It is positive semidefinite for every A. For A = [[0,1],[2,0]], the (0,0) entries of Aᴴ A and A Aᴴ are 4 and 1. Thus A is nonnormal and the universal equivalence on the closed interval is false.

**Theorem 1.4 (Normality is characterized below a = 1).**

$$\forall (a: \mathbb{R}), (\frac{1}{2} \le a) \Rightarrow ((a < 1) \Rightarrow (\forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix.PosSemidef}\left(\operatorname{D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation.block}\left((fun (x: \mathbb{R}) \mapsto x^{2 \cdot a}), (fun (x: \mathbb{R}) \mapsto x^{2 \cdot (1 - a)}), A\right)\right)) \Leftrightarrow (\operatorname{Matrix.conjTranspose}\left(A\right) \cdot A = A \cdot \operatorname{Matrix.conjTranspose}\left(A\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.below_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Feng Zhang; Hefang Jing (2025). *More inequalities for positive semidefinite matrices*. DOI: [10.13001/ela.2025.9201](https://doi.org/10.13001/ela.2025.9201). URL: <https://doi.org/10.13001/ela.2025.9201>.

*Commentary.*

An SVD writes A = V D Wᴴ with nonnegative diagonal D. A unitary change of block coordinates gives diagonal corners D^(2a) and Uᴴ D^(2(1−a)) U, where U = Wᴴ V. Testing positivity with the column [-D^(1−2a),I] gives a positive semidefinite difference Uᴴ D^(2(1−a)) U − D^(2(1−a)). Its trace is zero, so the difference vanishes. Positive-exponent real-power injectivity on nonnegative singular values forces U to commute with D, which is equivalent to normality. Conversely the balanced block is the Gram matrix of [D^a,D^(1−a)]. The zero singular values obey the same identities because a < 1. The cited lower interval 0 ≤ a ≤ 1/2 is outside this theorem; infinite-dimensional operators are also outside its scope.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.below_one`
- Truth anchor: `D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.claimBelowOne`
- Truth anchor: `D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.result`
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree](../Information/RenyiInformationCombiningOrderThree.md)
- Dependency: [D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation](ZhangJingBlockNormalityRefutation.md)
