# Root Pulse Sharpness

## Abstract

The root-pulse chain attains the finite observation refinement bound exactly.

**Theorem 1.1 (Root-pulse sharpness certificate).**

$$\begin{gathered}\forall n \in \mathbb{N}, 2 \leq n \Rightarrow\\(\forall i, j, 0 \leq i < j \leq n-1, d_{q}(i, j) = i) \land\\d_{q}(n-2, n-1) = n-2 \land\\(\forall m, E_{m+1} \subset E_{m} \iff m < n-2) \land\\m_{*} = n-2 \land\\d_{max} = n-2 \land\\m_{*} \leq \lvert \operatorname{Fin}(n) \rvert-\lvert Bool \rvert \land\\m_{*} = \lvert \operatorname{Fin}(n) \rvert-\lvert Bool \rvert.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/RootPulseSharpness.root_pulse_sharpness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every chain size n at least two, the state carrier is Fin n. The update is constructed as truncated predecessor and the Boolean readout is true exactly at state zero. The displayed distance is the repository separationTime for those maps.

If i is below j, both readouts remain false before time i, while at time i the first trajectory reaches the root and the second does not. Pinned Mathlib's Nat.find_eq_iff therefore gives d_q(i,j)=i. The penultimate and last states supply the endpoint certificate.

At depth m, two distinct states remain related exactly when both lie strictly above m. Hence consecutive observation relations refine strictly exactly for m<n-2. The existing least-stability test and finite supremum then both evaluate to n-2.

The repository theorem finite_observation_refinement_and_stability_bound is applied to the surjective root readout. Its two final inequalities give the general class-count bound, and the constructed chain attains that bound because the Boolean readout has two values.

## References

- Truth anchor: `D5/S3/Observer/Separation/RootPulseSharpness.root_pulse_sharpness`
- Dependency: [D5/S3/Observer/Separation/FiniteObservationRefinementBound](FiniteObservationRefinementBound.md)
