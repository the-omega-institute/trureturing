# Energy tightness and trace-norm compactness

## Abstract

Compactness of complete singular-energy state sublevels in trace norm.

**Definition 1.1 (The entire energy sublevel).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{Reference}\left(H\right),\; \forall M \in Real,\; \forall rho \in \operatorname{TraceClass}\left(H\right),\; \operatorname{member}\left(rho, \operatorname{energySublevel}\left(T, M\right)\right) \Leftrightarrow \left(0 \le \operatorname{underlyingOperator}\left(rho\right) \land \left(\operatorname{Re}\left(\operatorname{trace}\left(rho\right)\right) = 1 \land \operatorname{spectralEnergy}\left(T, rho\right) \le \operatorname{ofReal}\left(M\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/TraceClass/EnergySublevelCompactness.energySublevel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors; Tom Ole Diem (2026). *Trace ideals, finite orthogonal compression and complete metric compactness*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace>.

*Commentary.*

The set consists of all actual positive trace-one operators with spectral energy at most ofReal M. Its topology is the genuine trace-class Banach topology. The reference is any positive trace-class contraction and is not required to be faithful or normalized. Negative real bounds are clamped by ofReal; no emptiness claim for negative M is made.

**Theorem 1.2 (State-slot lower semicontinuity on the positive cone).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{Reference}\left(H\right),\; \operatorname{LowerSemicontinuousOn}\left(\operatorname{spectralEnergyAtReference}\left(T\right), \operatorname{positiveTraceClassCone}\left(H\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/EnergySublevelCompactness.lowerSemicontinuousOn_spectralEnergy_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors; Tom Ole Diem (2026). *Trace ideals, finite orthogonal compression and complete metric compactness*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace>.

*Commentary.*

For fixed T, every bounded regularized trace pairing is continuous in the trace-class argument. Applying ofReal and taking the supremum gives lower semicontinuity. On the positive cone the actual singular spectral energy equals this supremum. The equality is used only for positive rho; this assertion makes no lower-semicontinuity claim on arbitrary nonpositive operators.

**Theorem 1.3 (Closedness of the complete state sublevel).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{Reference}\left(H\right),\; \forall M \in Real,\; \operatorname{IsClosed}\left(\operatorname{energySublevel}\left(T, M\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/EnergySublevelCompactness.isClosed_energySublevel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors; Tom Ole Diem (2026). *Trace ideals, finite orthogonal compression and complete metric compactness*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace>.

*Commentary.*

The positive cone is closed through the continuous trace-norm-to-operator inclusion. The normalization equation is closed through the bounded trace pairing with the identity. State-slot lower semicontinuity on the positive cone gives a relatively closed energy sublevel. Intersecting these three conditions proves ambient trace-norm closedness.

**Theorem 1.4 (Uniform finite compression covers).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{Reference}\left(H\right),\; \forall M \in Real,\; 0 \le M \Rightarrow \operatorname{TotallyBounded}\left(\operatorname{energySublevel}\left(T, M\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/EnergySublevelCompactness.totallyBounded_energySublevel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors; Tom Ole Diem (2026). *Trace ideals, finite orthogonal compression and complete metric compactness*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace>.

*Commentary.*

Select the native full Set-index spectral basis of T together with its summable nonnegative eigenvalues s. For R>0 the indices with s_i at least exp(-R) form a finite set. Outside this set, singularLog(s_i) is at least R, including s_i=0 where singularLog is infinity. Summation in ENNReal before any conversion to real numbers gives R q<=M for the actual discarded state mass q. The noncommuting finite-compression estimate gives trace-norm error at most 2 sqrt(M/R). Compressed states lie in one compact image of the finite-dimensional trace-norm unit ball. A finite cover of this image and the uniform error bound give a finite cover of the entire sublevel. Arbitrary kernel fibers, M=0 and empty sublevels remain included.

**Theorem 1.5 (Trace-norm compactness of the entire energy sublevel).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{Reference}\left(H\right),\; \forall M \in Real,\; 0 \le M \Rightarrow \operatorname{IsCompact}\left(\operatorname{energySublevel}\left(T, M\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/EnergySublevelCompactness.isCompact_energySublevel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors; Tom Ole Diem (2026). *Trace ideals, finite orthogonal compression and complete metric compactness*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace>.

*Commentary.*

Closedness and total boundedness in the complete trace-class carrier imply compactness. The argument imposes no separability, finite ambient dimension, spectral enumeration, commutation or prior compactness assumption. This is a state-family compactness result for one reference; construction of a common continuous reference and a full unbounded Hamiltonian requires separate results.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/EnergySublevelCompactness.energySublevel`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/EnergySublevelCompactness.isClosed_energySublevel`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/EnergySublevelCompactness.isCompact_energySublevel`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/EnergySublevelCompactness.lowerSemicontinuousOn_spectralEnergy_state`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/EnergySublevelCompactness.totallyBounded_energySublevel`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/FiniteCompression](FiniteCompression.md)
