# Fuchs's physical-basis logarithm question is false

## Abstract

A faithful qutrit pair refutes a physical-basis diagonalization of Fuchs's logarithm argument.

Fuchs asks in §3.5.3 whether a basis can make the matrix in the logarithm of equation (3.244) diagonal. The construction below uses the Kronecker sum from equation (3.237), the inverse of the continuous-functional-calculus square root, and unitary conjugation.

**Definition 1.1 (The Kronecker sum).**

$$\forall (d: \mathbb{N}), (\forall (X: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation.ksum}\left(X\right) = (\operatorname{Matrix.kroneckerMap}\left((\lambda (x: \mathbb{C}) \mapsto ((\lambda (y: \mathbb{C}) \mapsto ((x) \cdot (y))))), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), X\right)) + (\operatorname{Matrix.kroneckerMap}\left((\lambda (x: \mathbb{C}) \mapsto ((\lambda (y: \mathbb{C}) \mapsto ((x) \cdot (y))))), \operatorname{Matrix.map}\left(X, \operatorname{star}\right), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))\right))))$$

*Formalization.* `D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.ksum` (`✓ std3`).

*Citation.* Christopher A. Fuchs (1996). *Distinguishability and Accessible Information in Quantum Theory*. URL: <https://arxiv.org/abs/quant-ph/9601020v1>.

*Commentary.*

For a complex square matrix X indexed by Fin d, ksum X is the sum of the identity tensor X and the entrywise-starred X tensor the identity. This is the operator form of Fuchs's Kronecker sum.

**Definition 1.2 (The matrix in the logarithm).**

$$\forall (d: \mathbb{N}), (\forall (rho0: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (rho1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (t: \mathbb{R}), (\operatorname{D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation.logArg}\left(rho0, rho1, t\right) = ((1: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right)) \times (\operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right)) \times (\operatorname{Fin}\left(d\right)), \mathbb{C}\right))) + (\operatorname{smul}\left((t: \mathbb{C}), (((\operatorname{CFC.sqrt}\left(\operatorname{D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation.ksum}\left(rho0\right)\right))^{-1}) \cdot (\operatorname{D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation.ksum}\left((rho1) - (rho0)\right))) \cdot ((\operatorname{CFC.sqrt}\left(\operatorname{D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation.ksum}\left(rho0\right)\right))^{-1})\right))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.logArg` (`✓ std3`).

*Citation.* Christopher A. Fuchs (1996). *Distinguishability and Accessible Information in Quantum Theory*. URL: <https://arxiv.org/abs/quant-ph/9601020v1>.

*Commentary.*

logArg is the identity plus t times the conjugated Kronecker difference, with both conjugations given by the inverse of the continuous-functional-calculus square root of ksum rho0.

**Definition 1.3 (The physical-basis diagonalization question).**

$$\forall (d: \mathbb{N}), (\forall (rho0: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (rho1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), ((\operatorname{Matrix.PosDef}\left(rho0\right)) \Rightarrow ((\operatorname{Matrix.PosDef}\left(rho1\right)) \Rightarrow ((\operatorname{Matrix.trace}\left(rho0\right) = 1) \Rightarrow ((\operatorname{Matrix.trace}\left(rho1\right) = 1) \Rightarrow ((\operatorname{Matrix.det}\left((rho1) - (rho0)\right) \ne 0) \Rightarrow (\forall (t: \mathbb{R}), ((0 < t) \Rightarrow ((t \le 1) \Rightarrow (\exists (U: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), ((U \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)) \land (\operatorname{Matrix.IsDiag}\left(\operatorname{D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation.logArg}\left(((\operatorname{star}\left(U\right)) \cdot (rho0)) \cdot (U), ((\operatorname{star}\left(U\right)) \cdot (rho1)) \cdot (U), t\right)\right))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.claim` (`✓ std3`).

*Citation.* Christopher A. Fuchs (1996). *Distinguishability and Accessible Information in Quantum Theory*. URL: <https://arxiv.org/abs/quant-ph/9601020v1>.

*Commentary.*

Fuchs's source sentence is: "An interesting open question is whether there exists a basis in which to represent the operators ρ̂₀, ρ̂₁, etc., so that the matrix appearing in the logarithm above is diagonal. If so, this would greatly simply the computation of L(t)." (after equation (3.244), §3.5.3, pp. 77–78). The Lean proposition asks for a unitary basis change for every positive-definite trace-one pair with invertible difference and every t in (0,1].

**Theorem 1.4 (The qutrit counterexample).**

$$\neg (\forall (d: \mathbb{N}), (\forall (rho0: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (rho1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), ((\operatorname{Matrix.PosDef}\left(rho0\right)) \Rightarrow ((\operatorname{Matrix.PosDef}\left(rho1\right)) \Rightarrow ((\operatorname{Matrix.trace}\left(rho0\right) = 1) \Rightarrow ((\operatorname{Matrix.trace}\left(rho1\right) = 1) \Rightarrow ((\operatorname{Matrix.det}\left((rho1) - (rho0)\right) \ne 0) \Rightarrow (\forall (t: \mathbb{R}), ((0 < t) \Rightarrow ((t \le 1) \Rightarrow (\exists (U: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), ((U \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)) \land (\operatorname{Matrix.IsDiag}\left(\operatorname{D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation.logArg}\left(((\operatorname{star}\left(U\right)) \cdot (rho0)) \cdot (U), ((\operatorname{star}\left(U\right)) \cdot (rho1)) \cdot (U), t\right)\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christopher A. Fuchs (1996). *Distinguishability and Accessible Information in Quantum Theory*. URL: <https://arxiv.org/abs/quant-ph/9601020v1>.

*Commentary.*

Take rho0 = diag(1/2,1/3,1/6) and rho1 = (1/16)[[7,-1,0],[-1,5,0],[0,0,4]]. Both matrices are positive definite with trace one, and the determinant of rho1-rho0 is -1/4608.

The -1/4 eigenspace of the normalized Kronecker difference is the line through the vectorization of M = [[1,sqrt(5/6),0],[sqrt(5/6),sqrt(2/3),0],[0,0,0]]. Its upper-left two-by-two minor is sqrt(2/3)-5/6, which is nonzero. Every column induced by a physical unitary has zero value for that minor, so no physical unitary conjugation makes the logarithm argument diagonal.

Thus the source's universal basis question is refuted by a faithful noncommuting qutrit pair. Arbitrary unitary diagonalization on the enlarged tensor space and the commuting sufficient case remain separate statements.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.ksum`
- Truth anchor: `D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.logArg`
- Truth anchor: `D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.result`
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Resource/LogDet/PathSpectralClassical](../../Resource/LogDet/PathSpectralClassical.md)
