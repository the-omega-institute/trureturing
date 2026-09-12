# Last-Tail Mass and Circuit Residuals

## Abstract

Local residual transitions determine all coefficients of a fixed-unitary circuit.

A and K are finite types with decidable equality. Space(K) is the complex Euclidean space, and Unitary(A x K) is its physical register unitary group. Word(A,n) consists of functions Fin(n) to A. The multiset occ(w) records the occupation of w. C(U,n,t,z,w,k) denotes the coefficient (w,k) of the actual circuit with the constant schedule U, n slots and starting time t. J(blank,n,x) initializes all slots with blank and the memory with x. B(blank,x) inserts the memory into one fresh blank slot. coefficient(U,v,(i,k)) means the (i,k) coordinate of U(v). sector(n,a,w) is the complex inverse square root of multiplicity(n,a) when occ(w)=a, and is zero otherwise; multiplicity counts actual occupation words.

**Definition 1.1 (Last-tail multiplicity).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall q \in A,\; \forall b \in Multiset\left(A\right),\; lastTailMass\left(q, b\right) = divideR\left(castR\left(tailCount\left(q, b\right)\right) \cdot castR\left(multiplicity\left(card\left(b\right), b\right)\right), castR\left(card\left(b\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/ResidualCalculus.lastTailMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

tailCount(q,b), also written R(q,b), sums the counts of letters other than q. multiplicity(n,b) counts occupation-b words of length n. castR is the natural-number inclusion into the reals and divideR is real division, including division by zero. Last-tail multiplicity is therefore defined for every b.

Step(a,blank,U,r) means that for every nonzero b<=a and every i:A and k:K, the (i,k) coefficient of U(B(blank,r(b))) equals r(erase(b,i))(k) if i belongs to b, and equals zero otherwise. Here r maps multisets to Space(K). IndicatorEq(c,b,v) means v if c=b and zero otherwise.

**Theorem 1.2 (Local residual equations determine the output).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \land \left(Fintype\left(K\right) \land DecidableEq\left(K\right)\right)\right) \Rightarrow \left(\forall blank \in A,\; \forall U \in Unitary\left(Prod\left(A, K\right)\right),\; \forall a \in Multiset\left(A\right),\; \forall r \in Function\left(Multiset\left(A\right), Space\left(K\right)\right),\; \forall f \in Space\left(K\right),\; \left(r\left(0\right) = f \land \left(\forall b \in Multiset\left(A\right),\; \left(b \le a \land b \ne 0\right) \Rightarrow \left(\forall i \in A,\; \forall k \in K,\; coefficient\left(U, blankMemory\left(blank, r\left(b\right)\right), pair\left(i, k\right)\right) = if\left(i \in b, r\left(erase\left(b, i\right), k\right), 0\right)\right)\right)\right) \Rightarrow \left(\forall n \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall b \in Multiset\left(A\right),\; \left(card\left(b\right) = n \land b \le a\right) \Rightarrow \left(\forall w \in Word\left(A, n\right),\; \forall k \in K,\; C\left(U, n, t, J\left(blank, n, r\left(b\right)\right), w, k\right) = IndicatorEq\left(occ\left(w\right), b, f\left(k\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/ResidualCalculus.circuit_output_of_residuals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the number of slots uses the actual circuit recursion. A legal first letter erases one occurrence from the remaining multiset; an absent first letter makes the coefficient zero. The empty word uses r(0)=f. This includes all legal and illegal words.

**Theorem 1.3 (Normalized equal-phase occupation output).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \land \left(Fintype\left(K\right) \land DecidableEq\left(K\right)\right)\right) \Rightarrow \left(\forall blank \in A,\; \forall U \in Unitary\left(Prod\left(A, K\right)\right),\; \forall a \in Multiset\left(A\right),\; \forall r \in Function\left(Multiset\left(A\right), Space\left(K\right)\right),\; \forall f \in Space\left(K\right),\; \left(r\left(0\right) = f \land \left(\forall b \in Multiset\left(A\right),\; \left(b \le a \land b \ne 0\right) \Rightarrow \left(\forall i \in A,\; \forall k \in K,\; coefficient\left(U, blankMemory\left(blank, r\left(b\right)\right), pair\left(i, k\right)\right) = if\left(i \in b, r\left(erase\left(b, i\right), k\right), 0\right)\right)\right)\right) \Rightarrow \left(\forall w \in Word\left(A, card\left(a\right)\right),\; \forall k \in K,\; C\left(U, card\left(a\right), 0, J\left(blank, card\left(a\right), scale\left(inverse\left(sqrtC\left(multiplicity\left(card\left(a\right), a\right)\right)\right), r\left(a\right)\right)\right), w, k\right) = sector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/ResidualCalculus.normalized_output_of_residuals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

InvRoot(a) is the complex inverse of the square root of M(card(a),a). The sector coefficient is this same positive real amplitude on words of occupation a and zero on every other word. Linearity transfers the unnormalized coefficient identity to the scaled input.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/ResidualCalculus.circuit_output_of_residuals`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/ResidualCalculus.lastTailMass`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/ResidualCalculus.normalized_output_of_residuals`
- Dependency: [D5/S3/Quantum/StationaryPreparation/PaddingMemory](PaddingMemory.md)
