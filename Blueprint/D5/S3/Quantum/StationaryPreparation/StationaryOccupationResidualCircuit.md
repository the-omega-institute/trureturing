# Stationary Occupation Residual Circuits

## Abstract

Concrete last-tail residual vectors and their normalized physical output.

A and K are finite types with decidable equality. Space(K) is the complex Euclidean space, and Unitary(A x K) is its physical register unitary group. Word(A,n) consists of functions Fin(n) to A. The multiset occ(w) records the occupation of w. C(U,n,t,z,w,k) denotes the coefficient (w,k) of the actual circuit with the constant schedule U, n slots and starting time t. J(blank,n,x) initializes all slots with blank and the memory with x. B(blank,x) inserts the memory into one fresh blank slot. coefficient(U,v,(i,k)) means the (i,k) coordinate of U(v). sector(n,a,w) is the complex inverse square root of multiplicity(n,a) when occ(w)=a, and is zero otherwise; multiplicity counts actual occupation words.

**Definition 1.1 (Changing only the head count).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall q \in A,\; \forall b \in Multiset\left(A\right),\; \forall h \in \mathbb{N},\; headSlice\left(q, b, h\right) = addMultiset\left(replicate\left(h, q\right), filterNotEqual\left(b, q\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualCircuit.headSlice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

filterNotEqual(b,q) retains precisely the letters different from q. Thus the head count is h and every tail count is unchanged. R(q,b) denotes tailCount(q,b); lastTailMass(q,b) is R(q,b) times the occupation multiplicity divided by card(b), in the real numbers.

**Theorem 1.2 (Removing one head letter).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall q \in A,\; \forall b \in Multiset\left(A\right),\; \forall h \in \mathbb{N},\; \left(0 < h \land 0 < R\left(q, b\right)\right) \Rightarrow sqrtC\left(headProbability\left(h, R\left(q, b\right)\right)\right) \cdot sqrtC\left(lastTailMass\left(q, headSlice\left(q, b, h\right)\right)\right) = sqrtC\left(lastTailMass\left(q, headSlice\left(q, b, h - 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualCircuit.head_slice_head_amplitude` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

sqrtC is the nonnegative real square root included in the complex numbers. The multiplicity erase identity proves this equality, including the case R(q,b)=1. Subtraction in the head index is natural subtraction.

**Definition 1.3 (Residual memory vectors).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall q \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in Multiset\left(A\right),\; \left(\forall hb \in b \le a,\; \forall hr \in 0 < tailCount\left(q, b\right),\; paddingResidual\left(q, a, b\right) = \sum_{h:Fin\left(succ\left(count\left(b, q\right)\right)\right)}{scale\left(sqrtC\left(lastTailMass\left(q, headSlice\left(q, b, val\left(h\right)\right)\right)\right), basis\left(some\left(pair\left(residualPositiveTail\left(q, a, b, hb, hr\right), residualHeadIndex\left(q, a, b, hb, h\right)\right)\right)\right)\right)}\right) \land \left(\left(\left(b \le a \land tailCount\left(q, b\right) = 0\right) \Rightarrow paddingResidual\left(q, a, b\right) = basis\left(none\left(\right)\right)\right) \land \left(not\left(b \le a\right) \Rightarrow paddingResidual\left(q, a, b\right) = 0\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualCircuit.paddingResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive-tail branch sums over every h in Fin(count(b,q)+1). residualPositiveTail is the bounded tail function i maps to count(b,i), with its nonzero proof; residualHeadIndex embeds h into Fin(count(a,q)+1). The displayed hb and hr bind these proof arguments. The vector is the sink when the tail is empty, and zero outside b<=a. sqrtC includes the nonnegative real square root in the complex numbers; scale denotes complex scalar multiplication.

**Definition 1.4 (Residuals in physical memory coordinates).**

$$\forall A \in Type,\; \left(\left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \land Nonempty\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall b \in Multiset\left(A\right),\; physicalResidual\left(a, b\right) = coordinateEmbedding\left(toEmbedding\left(physicalMemoryEquiv\left(a\right)\right), paddingResidual\left(maximalHead\left(a\right), a, b\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualCircuit.physicalResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maximal head has maximum occupation count. physicalMemoryEquiv identifies the padding memory with Fin(d), where d is the product of count(a,i)+1 minus the maximum count. coordinateEmbedding transports the actual residual vector isometrically.

Step(a,blank,U,r) means that for every nonzero b<=a and every i:A and k:K, the (i,k) coefficient of U(B(blank,r(b))) equals r(erase(b,i))(k) if i belongs to b, and equals zero otherwise. Here r maps multisets to Space(K). IndicatorEq(c,b,v) means v if c=b and zero otherwise.

**Theorem 1.5 (The exact output fixes the initial norm).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \land \left(Fintype\left(K\right) \land DecidableEq\left(K\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Prod\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall sink \in K,\; \left(\forall w \in Word\left(A, card\left(a\right)\right),\; \forall k \in K,\; C\left(U, card\left(a\right), 0, J\left(blank, card\left(a\right), x\right), w, k\right) = sector\left(card\left(a\right), a, w\right) \cdot basis\left(sink, k\right)\right) \Rightarrow norm\left(x\right) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualCircuit.initial_norm_of_sector_output` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occupation sector has norm one. Embedding it into the sink memory preserves that norm, while the actual unitary circuit and initialization preserve the norm of x. No initial normalization hypothesis is used.

**Theorem 1.6 (Concrete transitions suffice for attainment).**

$$\forall A \in Type,\; \left(\left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \land Nonempty\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; ResidualStep\left(a\right) \Rightarrow Target\left(a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualCircuit.target_of_residual_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ResidualStep is Step for the maximal-capacity head as blank, the fixed padding unitary, and physicalResidual(a,-). Target(a) asserts existence of one blank, one unitary on A x Fin(d), and unit initial and final memories, with every coefficient equal to sector(card(a),a,w) times the final memory; d is product(count(a,i)+1) minus the maximum count. The initial memory is InvRoot(a) times physicalResidual(a,a), and the terminal memory is the sink. The argument also includes the zero multiset.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualCircuit.headSlice`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualCircuit.head_slice_head_amplitude`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualCircuit.initial_norm_of_sector_output`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualCircuit.paddingResidual`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualCircuit.physicalResidual`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualCircuit.target_of_residual_step`
- Dependency: [D5/S3/Quantum/StationaryPreparation/ResidualCalculus](ResidualCalculus.md)
- Dependency: [D5/S3/Quantum/StationaryPreparation/StationaryOccupationPadding](StationaryOccupationPadding.md)
