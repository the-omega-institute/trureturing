# Finite Horizon Kernel Recurrence

## Abstract

Finite-horizon behavior kernels descend by one new coordinate, intersect to the complete kernel, and stabilize at the finite completion depth.

**Theorem 1.1 (Finite Horizon Kernel Succ iff).**

$$\forall Y: Type, O: Type, tau: Y \to Y, q: Y \to O, m: \mathbb{N}, y: Y, y': Y,\\{}(finiteHorizonKernel tau q (m + 1) y y' \Leftrightarrow finiteHorizonKernel tau q m y y' \land q ((tau^{[m + 1]}) y) = q ((tau^{[m + 1]}) y')).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.finite_horizon_kernel_succ_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding one horizon coordinate intersects the previous kernel with equality of the new terminal observation.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Finite Horizon Kernel Antitone).**

$$\forall Y: Type, O: Type, tau: Y \to Y, q: Y \to O, m: \mathbb{N}, n: \mathbb{N},\\{}(m \leq n) \Rightarrow\\{}(finiteHorizonKernel tau q n \leq finiteHorizonKernel tau q m).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.finite_horizon_kernel_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Longer observation horizons yield finer kernels.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Complete Kernel eq I Inf Finite Horizon).**

$$\forall Y: Type, O: Type, tau: Y \to Y, q: Y \to O,\\{}(Setoid.ker (completeItinerary tau q) = iInf m, finiteHorizonKernel tau q m).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.complete_kernel_eq_iInf_finite_horizon` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete behavior kernel is the infimum of all finite-horizon kernels.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Finite Horizon First New Coordinate Strict).**

$$\forall Y: Type, O: Type, tau: Y \to Y, q: Y \to O, m: \mathbb{N}, y: Y, y': Y,\\{}(finiteHorizonKernel tau q m y y') \land (q ((tau^{[m + 1]}) y) \neq q ((tau^{[m + 1]}) y')) \Rightarrow\\{}(finiteHorizonKernel tau q (m + 1) < finiteHorizonKernel tau q m).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.finite_horizon_first_new_coordinate_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A first separating terminal coordinate certifies strict refinement at the next finite horizon.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Finite Horizon Stabilizes At Completion Depth).**

$$\forall Y: Type, O: Type, tau: Y \to Y, q: Y \to O, [\operatorname{Fintype}\left(Y\right)],\\{}(finiteHorizonKernel tau q (completionDepth tau q) = Setoid.ker (completeItinerary tau q)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.finite_horizon_stabilizes_at_completionDepth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite state space, the canonical completion depth already has the complete infinite-horizon kernel.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.complete_kernel_eq_iInf_finite_horizon`
- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.finite_horizon_first_new_coordinate_strict`
- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.finite_horizon_kernel_antitone`
- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.finite_horizon_kernel_succ_iff`
- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.finite_horizon_stabilizes_at_completionDepth`
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../Prediction/ItineraryCompletion.md)
