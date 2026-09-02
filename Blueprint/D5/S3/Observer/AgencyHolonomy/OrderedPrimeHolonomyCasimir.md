# Ordered-Prime Holonomy Casimir

## Abstract

The ordered-prime observer trace cancels linear phase and retains the squared winding response.

**Theorem 1.1 (Linear cancellation and quadratic winding readout).**

$$\forall iota \in \operatorname{Type}, word \in iota \to \operatorname{List}\left(\operatorname{UnramifiedPrime}\left(\right)\right), winding \in iota \to \operatorname{ZMod}\left(0\right), s \in \mathbb{R},\; \left(\operatorname{Countable}\left(iota\right) \land \left(\left(\forall i \in iota,\; goldenPrimeHolonomy\left(word\left(i\right)\right) = \operatorname{r}\left(winding\left(i\right)\right)\right) \land \left(\operatorname{Summable}\left((x: {iota \times \mathbb{N}} \mapsto \operatorname{abs}\left(\operatorname{observerOrbitAmplitude}\left(word, s, x\right)\right))\right) \land \left(\operatorname{Summable}\left((x: {iota \times \mathbb{N}} \mapsto \operatorname{abs}\left(\operatorname{observerOrbitAmplitude}\left(word, s, x\right)\right) \cdot 2 \cdot \operatorname{abs}\left(\operatorname{repeatedOrbitWinding}\left(winding, x\right)\right))\right) \land \operatorname{Summable}\left((x: {iota \times \mathbb{N}} \mapsto \operatorname{abs}\left(\operatorname{observerOrbitAmplitude}\left(word, s, x\right)\right) \cdot 2 \cdot \operatorname{repeatedOrbitWinding}\left(winding, x\right)^{2})\right)\right)\right)\right)\right) \Rightarrow \left(\left(\forall i \in iota, m \in \mathbb{N},\; -\operatorname{iteratedDeriv}\left(2, (theta: \mathbb{R} \mapsto \operatorname{re}\left(\operatorname{trace}\left(\operatorname{dihedralObserverRepresentation}\left(theta\right)\left(goldenPrimeHolonomy\left(word\left(i\right)\right)^{m}\right)\right)\right)), 0\right) = 2 \cdot m^{2} \cdot \operatorname{integerCast}\left(winding\left(i\right)\right)^{2}\right) \land \left(\operatorname{iteratedDeriv}\left(1, \operatorname{orderedPrimeObserverLog}\left(word, s\right), 0\right) = 0 \land \left(-\operatorname{iteratedDeriv}\left(2, \operatorname{orderedPrimeObserverLog}\left(word, s\right), 0\right) = \operatorname{tsum}\left((x: {iota \times \mathbb{N}} \mapsto \operatorname{observerOrbitAmplitude}\left(word, s, x\right) \cdot 2 \cdot \operatorname{repeatedOrbitWinding}\left(winding, x\right)^{2})\right) \land \left(\forall x \in {iota \times \mathbb{N}},\; 0 \le \operatorname{observerOrbitAmplitude}\left(word, s, x\right) \cdot 2 \cdot \operatorname{repeatedOrbitWinding}\left(winding, x\right)^{2}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/OrderedPrimeHolonomyCasimir.ordered_prime_holonomy_casimir` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each primitive orbit carries its actual ordered prime word and an integral rotation winding. The orientation premise identifies the imported prime-word holonomy with that rotation in the infinite dihedral group.

The observer uses the two conjugate Fourier channels, the product prime weight, and every positive repeat. Summability of the weight and its first two winding moments supplies the absolute-convergence region.

The local negative second trace derivative is twice the squared repeated winding. Globally the first derivative vanishes, while the negative second derivative is the nonnegative weighted sum of all repeated squared windings.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/OrderedPrimeHolonomyCasimir.ordered_prime_holonomy_casimir`
- Dependency: [D5/S3/Observer/AgencyHolonomy/GoldenScalarDihedralBlindness](GoldenScalarDihedralBlindness.md)
- Dependency: [D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow](PrimeFrequencyPhaseFlow.md)
- Dependency: [D5/S3/Quantum/FiniteDimensional](../../Quantum/FiniteDimensional.md)
