# Semi-nonnegative maps can exhibit information backflow

## Abstract

A semi-nonnegative qutrit map that is not semi-positive doubles trace distance between two states in a common Kraus context.

Matrices have complex entries and indices in Fin(d), the integers from zero through d minus one. LinearMap(C,M,M) denotes the complex-linear maps on the displayed matrix space M. The adjoint is conjugate transpose. Matrix.PosSemidef and Matrix.PosDef mean positive semidefinite and positive definite, respectively. A density matrix is positive semidefinite with complex trace one; these two conditions are written explicitly below. The bracketed Fintype assumptions supply finite enumerations, and every sum ranges over its entire displayed index type.

**Definition 1.1 (Hermiticity and trace preservation).**

$$\forall d \in \mathbb{N},\; \forall Psi \in \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; \operatorname{IsHPTP}\left(Psi\right) \Leftrightarrow ((\forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; Psi\left(\operatorname{Matrix.conjTranspose}\left(X\right)\right) = \operatorname{Matrix.conjTranspose}\left(Psi\left(X\right)\right)) \land (\forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{Matrix.trace}\left(Psi\left(X\right)\right) = \operatorname{Matrix.trace}\left(X\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.IsHPTP` (`✓ std3`).

*Citation.* Ningping Cao; Maxwell Fitzsimmons; Zachary Mann; Rajesh Pereira; Raymond Laflamme (2023). *Quantum Maps Between CPTP and HPTP*. URL: <https://arxiv.org/abs/2308.01894v1>.

*Commentary.*

For a complex-linear map, Hermiticity preservation is expressed by commuting with the adjoint on every matrix. Trace preservation also holds on every matrix. This is the HPTP setting of Definitions 1 and 2 and Theorem 2.

**Definition 1.2 (Semi-positivity).**

$$\forall d \in \mathbb{N},\; \forall Psi \in \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; \operatorname{IsSemiPositive}\left(Psi\right) \Leftrightarrow (\exists rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; ((\operatorname{Matrix.PosSemidef}\left(rho\right)) \land (\operatorname{Matrix.trace}\left(rho\right) = 1)) \land ((\operatorname{Matrix.PosDef}\left(rho\right)) \land (((\operatorname{Matrix.PosSemidef}\left(Psi\left(rho\right)\right)) \land (\operatorname{Matrix.trace}\left(Psi\left(rho\right)\right) = 1)) \land (\operatorname{Matrix.PosDef}\left(Psi\left(rho\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.IsSemiPositive` (`✓ std3`).

*Citation.* Ningping Cao; Maxwell Fitzsimmons; Zachary Mann; Rajesh Pereira; Raymond Laflamme (2023). *Quantum Maps Between CPTP and HPTP*. URL: <https://arxiv.org/abs/2308.01894v1>.

*Commentary.*

Definition 1 requires a positive-definite density matrix whose image is also a positive-definite density matrix. Positive definiteness is equivalent to invertibility for a density matrix. The predicate itself imposes no Hermiticity or trace preservation on the map; those are separate hypotheses.

**Definition 1.3 (Semi-nonnegativity).**

$$\forall d \in \mathbb{N},\; \forall Psi \in \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; \operatorname{IsSemiNonnegative}\left(Psi\right) \Leftrightarrow (\exists rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; ((\operatorname{Matrix.PosSemidef}\left(rho\right)) \land (\operatorname{Matrix.trace}\left(rho\right) = 1)) \land ((\operatorname{Matrix.PosSemidef}\left(Psi\left(rho\right)\right)) \land (\operatorname{Matrix.trace}\left(Psi\left(rho\right)\right) = 1)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.IsSemiNonnegative` (`✓ std3`).

*Citation.* Ningping Cao; Maxwell Fitzsimmons; Zachary Mann; Rajesh Pereira; Raymond Laflamme (2023). *Quantum Maps Between CPTP and HPTP*. URL: <https://arxiv.org/abs/2308.01894v1>.

*Commentary.*

Definition 2 requires a density matrix with a density image, allowing singular matrices. Hermiticity and trace preservation are separate hypotheses in the statement below. Theorem 2 characterizes this property for HPTP maps by a pair of channels with composition Psi after Phi equal to Xi.

**Definition 1.4 (Trace distance).**

$$\forall d \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall sigma \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{traceDistance}\left(rho, sigma\right) = \frac{\Vert rho - sigma\Vert_{1}}{2} = \frac{\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{CFC.sqrt}\left(\operatorname{Matrix.conjTranspose}\left(rho - sigma\right) \cdot \left(rho - sigma\right)\right)\right)\right)}{2}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.traceDistance` (`✓ std3`).

*Citation.* Ningping Cao; Maxwell Fitzsimmons; Zachary Mann; Rajesh Pereira; Raymond Laflamme (2023). *Quantum Maps Between CPTP and HPTP*. URL: <https://arxiv.org/abs/2308.01894v1>.

*Commentary.*

Trace distance is one half of the trace norm of the difference. The trace norm is the real part of the trace of the positive square root of the adjoint product, as displayed explicitly. CFC.sqrt denotes that positive matrix square root. This is the trace-distance meaning of information backflow in the Outlook and its cited works.

**Definition 1.5 (The no-backflow conjunct).**

$$\operatorname{claim} \Leftrightarrow (\forall d \in \mathbb{N},\; \forall Psi \in \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; ((\operatorname{IsHPTP}\left(Psi\right)) \land ((\operatorname{IsSemiNonnegative}\left(Psi\right)) \land (\neg (\operatorname{IsSemiPositive}\left(Psi\right))))) \Rightarrow (\forall iota \in \operatorname{Type},\; \forall kappa \in \operatorname{Type},\; [\operatorname{Fintype}\left(iota\right)] [\operatorname{Fintype}\left(kappa\right)] \forall K \in iota \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall L \in kappa \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\sum_{r:iota} (\operatorname{Matrix.conjTranspose}\left(K\left(r\right)\right) \cdot K\left(r\right)) = 1) \Rightarrow ((\sum_{r:kappa} (\operatorname{Matrix.conjTranspose}\left(L\left(r\right)\right) \cdot L\left(r\right)) = 1) \Rightarrow ((\forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; Psi\left(\sum_{r:iota} (K\left(r\right) \cdot X \cdot \operatorname{Matrix.conjTranspose}\left(K\left(r\right)\right))\right) = \sum_{r:kappa} (L\left(r\right) \cdot X \cdot \operatorname{Matrix.conjTranspose}\left(L\left(r\right)\right))) \Rightarrow (\forall sigmaOne \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall sigmaTwo \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; ((\operatorname{Matrix.PosSemidef}\left(sigmaOne\right)) \land (\operatorname{Matrix.trace}\left(sigmaOne\right) = 1)) \Rightarrow (((\operatorname{Matrix.PosSemidef}\left(sigmaTwo\right)) \land (\operatorname{Matrix.trace}\left(sigmaTwo\right) = 1)) \Rightarrow (\operatorname{traceDistance}\left(\sum_{r:kappa} (L\left(r\right) \cdot sigmaOne \cdot \operatorname{Matrix.conjTranspose}\left(L\left(r\right)\right)), \sum_{r:kappa} (L\left(r\right) \cdot sigmaTwo \cdot \operatorname{Matrix.conjTranspose}\left(L\left(r\right)\right))\right) \le \operatorname{traceDistance}\left(\sum_{r:iota} (K\left(r\right) \cdot sigmaOne \cdot \operatorname{Matrix.conjTranspose}\left(K\left(r\right)\right)), \sum_{r:iota} (K\left(r\right) \cdot sigmaTwo \cdot \operatorname{Matrix.conjTranspose}\left(K\left(r\right)\right))\right))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.claim` (`✓ std3`).

*Citation.* Ningping Cao; Maxwell Fitzsimmons; Zachary Mann; Rajesh Pereira; Raymond Laflamme (2023). *Quantum Maps Between CPTP and HPTP*. URL: <https://arxiv.org/abs/2308.01894v1>.

*Commentary.*

The Outlook conjectures absence of information backflow for semi-nonnegative trace-preserving maps that are not semi-positive, also in higher dimensions. Here the map is complex-linear and HPTP. The claim quantifies over every dimension, every such map, every two normalized finite Kraus families K and L, and every two input density matrices. The composition hypothesis says that applying Psi after the K channel equals the L channel on every matrix, as in Theorem 2. The conclusion compares the two trace distances in this common channel context. It is the no-backflow conjunct; the separate assertion about nonuniqueness of the intermediate map is not part of this statement.

**Theorem 1.6 (A qutrit context doubles trace distance).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/cao-fitzsimmons-mann-pereira-laflamme-2023-semi-nonnegative-backflow-refutation` (refuted) by `D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cao-fitzsimmons-mann-pereira-laflamme-2023-semi-nonnegative-backflow-refutation","declaration_gid":"D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ningping Cao; Maxwell Fitzsimmons; Zachary Mann; Rajesh Pereira; Raymond Laflamme (2023). *Quantum Maps Between CPTP and HPTP*. URL: <https://arxiv.org/abs/2308.01894v1>.

*Commentary.*

Write a qutrit matrix as X = [[A,u],[v,c]], with A a two-by-two block. Set Psi(X) = [[2A - (tr A) I/2 + c I,u],[v,-c]], where I is the two-by-two identity. This map is complex-linear, commutes with the adjoint and preserves trace. It fixes diag(1/2,1/2,0), so it is semi-nonnegative. For a positive-definite input, c is strictly positive and the last diagonal entry of the image is -c. Thus no positive-definite density has a density image, and the map is not semi-positive.

Let P = diag(1,1,0) and let E(a,b) have entry one in row a, column b and zero elsewhere, using indices 1,2,3 in this paragraph. Define Xi(X) = P X P + x(3,3) P/2 and Phi(X) = Xi(X)/2 + (tr X) P/4. A Kraus family for Xi is (P,E(1,3)/2,E(1,3)/2,E(2,3)/2,E(2,3)/2). A Kraus family for Phi is (P/2,P/2,E(1,3)/2,E(2,3)/2,E(1,1)/2,E(1,2)/2,E(1,3)/2,E(2,1)/2,E(2,2)/2,E(2,3)/2). Both families have adjoint products summing to the qutrit identity, and Psi(Phi(X)) = Xi(X) for every matrix X.

Take the input states diag(5/8,1/8,1/4) and diag(1/8,5/8,1/4). Phi sends them to diag(5/8,3/8,0) and diag(3/8,5/8,0), whose trace distance is 1/4. Xi sends them to diag(3/4,1/4,0) and diag(1/4,3/4,0), whose trace distance is 1/2. The asserted inequality would therefore give 1/2 at most 1/4, a contradiction.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.IsHPTP`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.IsSemiNonnegative`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.IsSemiPositive`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.traceDistance`
- Dependency: [D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation](../Information/ChenKatoBrandaoTraceNormCMIRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation](OutputMaximalCoherenceTensorizationRefutation.md)
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](../../QuantumChannels/CoPRelativeQuantumnessRefutation.md)
