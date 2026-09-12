# Stationary Occupation Memory Attainment

## Abstract

A single repeated unitary attains the product-minus-maximum occupation memory dimension.

A is an arbitrary finite nonempty alphabet with decidable equality and a is an arbitrary multiset on A. Let d(a) be the product over i:A of count(a,i)+1, minus the maximum count. The dimension is a natural number. Space(I) and Unitary(I) are the actual complex Euclidean space and its linear isometry equivalences. Word(A,n) is Fin(n) to A, and L(a)=card(a).

Choose a head q of maximum capacity. A nonzero-tail memory index records the remaining tail occupation and a head index h. Emitting q decrements h, with the h=0 coefficient zero. Emitting a tail letter with at least two remaining tail letters decrements that tail coordinate and preserves h. With exactly one tail letter remaining, only h=0 can emit it, and the transition enters the sink.

**Theorem 1.1 (Every legal positive-tail transition has the prescribed residual).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall b \in Multiset\left(A\right),\; \left(b \le a \land 0 < tailCount\left(maximalHead\left(a\right), b\right)\right) \Rightarrow \left(\forall i \in A,\; i \in b \Rightarrow \left(\forall k \in Fin\left(d\left(a\right)\right),\; coefficient\left(physicalGate\left(a\right), blankMemory\left(maximalHead\left(a\right), physicalResidual\left(a, b\right)\right), pair\left(i, k\right)\right) = physicalResidual\left(a, erase\left(b, i\right), k\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualStep.positive_residual_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

PositiveResidualStep(a) means: for every b<=a with positive tail count, every i belonging to b, and every k:Fin(d(a)), the (i,k) coefficient of physicalGate(a) applied to a fresh q and physicalResidual(a,b) equals physicalResidual(a,erase(b,i))(k). The head case uses a successor reindexing of the finite sum. The two tail cases use the multiplicity square-root identities and the sink boundary.

**Theorem 1.2 (The exact proposed dimension is attained by one fixed gate).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \exists blank \in A,\; \exists U \in Unitary\left(Prod\left(A, Fin\left(d\left(a\right)\right)\right)\right),\; \exists x \in Space\left(Fin\left(d\left(a\right)\right)\right),\; \exists f \in Space\left(Fin\left(d\left(a\right)\right)\right),\; norm\left(x\right) = 1 \land \left(norm\left(f\right) = 1 \land \left(\forall w \in Word\left(A, L\left(a\right)\right),\; \forall k \in Fin\left(d\left(a\right)\right),\; C\left(U, L\left(a\right), 0, J\left(blank, L\left(a\right), x\right), w, k\right) = sector\left(L\left(a\right), a, w\right) \cdot f\left(k\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualStep.stationary_memory_dimension_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

C(U,L,0,J(blank,L,x),w,k) is the (w,k) coefficient of the actual L-slot circuit with the literal constant schedule U, acting on all slots initialized to blank and memory x. The same U and blank are used at every step. sector(L,a,w) equals the positive inverse square root of the number of occupation-a words on those words, and zero on all other words.

The residual transitions imply every word coefficient by induction. The normalized sector and the unitary circuit imply that the initial vector, the complex inverse square root of multiplicity(card(a),a) times physicalResidual(a,a), has norm one. The common final memory is the sink basis vector. This includes zero occupation and letters of zero capacity; all physical memory is Fin(d(a)).

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualStep.positive_residual_step`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualStep.stationary_memory_dimension_attained`
- Dependency: [D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualCircuit](StationaryOccupationResidualCircuit.md)
