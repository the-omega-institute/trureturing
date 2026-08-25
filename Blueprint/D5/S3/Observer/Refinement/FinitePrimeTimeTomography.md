# Finite Prime-Time Tomography

## Abstract

Complete prime-time separation on a finite state space has a finite witness.

**Theorem 1.1 (Complete separation has a finite window).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}[\operatorname{Finite}(X)], q: \mathbb{N} \to X \to O, T: X \to X,\\{}\operatorname{SeparatedByCompleteObservation}\left(q, T\right) \Rightarrow \exists J: \operatorname{Finset}\left(\mathbb{N}\right), m: \mathbb{N},\\{}\operatorname{Indist}\left(J, m, q, T\right) \subseteq \operatorname{diagonal}\left(X\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Refinement/FinitePrimeTimeTomography.finite_prime_time_tomography` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The relations arising from finite index sets and time horizons form a downward-directed family: the union of two index sets and the maximum of two horizons refine both original windows.

When the state space is finite, its set of binary relations is finite. A minimal member of the directed family is contained in every member, hence in the complete intersection and the equality diagonal. No primality or finite-output hypothesis is used.

**Theorem 1.2 (Complete separation is necessary).**

$$\neg\operatorname{SeparatedByCompleteObservation}\left(c, id\right) \land \neg\exists J: \operatorname{Finset}\left(\mathbb{N}\right), m: \mathbb{N}, \operatorname{Indist}\left(J, m, c, id\right) \subseteq \operatorname{diagonal}\left(\operatorname{Bool}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Refinement/FinitePrimeTimeTomography.complete_separation_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the two Boolean states, let every indexed readout be constant and let the transition be the identity. The pair of distinct states remains in every finite-window kernel.

It therefore remains in the complete intersection as well. Neither complete separation nor a separating finite window holds, showing that the separation premise cannot be removed.

**Theorem 1.3 (Finiteness is necessary).**

$$\neg\operatorname{Finite}(\mathbb{N}) \land \operatorname{SeparatedByCompleteObservation}\left(theta, id\right) \land \neg\exists J: \operatorname{Finset}\left(\mathbb{N}\right), m: \mathbb{N}, \operatorname{Indist}\left(J, m, theta, id\right) \subseteq \operatorname{diagonal}\left(\mathbb{N}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Refinement/FinitePrimeTimeTomography.finiteness_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the natural numbers, the threshold readout at index i records whether x is below i. All indices together separate distinct states, even with identity dynamics.

For any finite index set, its maximum and the next natural number give identical threshold values at every selected index. Thus no finite prime-time window separates the infinite carrier.

## References

- Truth anchor: `D5/S3/Observer/Refinement/FinitePrimeTimeTomography.complete_separation_is_necessary`
- Truth anchor: `D5/S3/Observer/Refinement/FinitePrimeTimeTomography.finite_prime_time_tomography`
- Truth anchor: `D5/S3/Observer/Refinement/FinitePrimeTimeTomography.finiteness_is_necessary`
- Dependency: [D5/S3/Observer/Refinement/BiaxialMonotoneRefinement](BiaxialMonotoneRefinement.md)
