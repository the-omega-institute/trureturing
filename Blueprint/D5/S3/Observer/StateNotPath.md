# Classical and Quantum Coherence Reachability

## Abstract

Classical diagonal iteration and a one-step Hadamard witness separate coherence reachability.

**Theorem 1.1 (Classical diagonal iterations preserve zero coherence).**

$$\begin{gathered}\forall c \in [0, 1],\\\forall n \in \mathbb{N},\\\forall \rho \in \operatorname{QubitMatrix},\\\operatorname{offDiag}(\rho)=0 \Rightarrow \operatorname{offDiag}((\operatorname{classicalDiagonalChannel}(c))^{n}(\rho))=0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/StateNotPath.classical_diagonal_iterates_off_diag_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a qubit matrix rho, offDiag(rho) is the ordered pair of entries rho(0,1) and rho(1,0). The classical diagonal channel at a real retention coefficient c in [0,1] is the existing phase-damping map: it preserves diagonal entries and scales each off-diagonal entry by c.

If offDiag(rho) is zero, induction over the standard finite function iterate shows that every later off-diagonal pair is zero. The statement quantifies over every coefficient, every finite iteration count, and every diagonal initial qubit matrix; no positivity or normalization premise is needed.

**Theorem 1.2 (One Hadamard step creates exact coherence).**

$$\begin{gathered}\operatorname{offDiag}(\operatorname{hadamardCoordinates}(\operatorname{basisZeroDensity}))=(\frac{1}{2}, \frac{1}{2}) \land \\\operatorname{offDiag}(\operatorname{hadamardCoordinates}(\operatorname{basisZeroDensity}))\neq 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/StateNotPath.hadamard_basis_zero_off_diag_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The computational basis density matrix has entries 1, 0, 0, 0 and therefore starts with zero coherence. Applying the existing normalized Hadamard coordinate conjugation once gives both off-diagonal entries exactly one half. Hence its offDiag pair is (1/2, 1/2), which is algebraically nonzero.

Together, the universal classical preservation theorem and this explicit one-step witness distinguish the two reachability mechanisms. The result is solely a finite two-by-two matrix certificate and introduces no new probability law or measurement premise.

## References

- Truth anchor: `D5/S3/Observer/StateNotPath.classical_diagonal_iterates_off_diag_eq_zero`
- Truth anchor: `D5/S3/Observer/StateNotPath.hadamard_basis_zero_off_diag_certificate`
