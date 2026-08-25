# Finiteness Is Not Immediate Degeneracy

## Abstract

Finite dynamics eventually cycle without forcing short periods, short transients, or rich readouts.

**Theorem 1.1 (Periodic structure does not determine readout richness).**

$$\exists tauLow: \mathbb{B} \to \mathbb{B}, tauHigh: \mathbb{B} \to \mathbb{B},\\qLow: \mathbb{B} \to \mathbb{B}, qHigh: \mathbb{B} \to \mathbb{B},\\Nonempty(PeriodicCore(tauLow) \equiv PeriodicCore(tauHigh)) \land\\minimalPeriod(tauLow, false) = minimalPeriod(tauHigh, false) \land\\\lvert periodicReadoutValues(tauLow, qLow) \rvert < \lvert periodicReadoutValues(tauHigh, qHigh) \rvert.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FunctionalGraphs/FinitenessIsNotImmediateDegeneracy.periodic_structure_does_not_determine_readout_richness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source leaves semantic quality undefined. The formal fallback measures only the number of readout values realized on the periodic core and introduces no quality axiom.

Two Boolean identity systems have equivalent periodic cores and equal minimal periods. A constant readout realizes one value, while the identity readout realizes both Boolean values.

**Theorem 1.2 (Finiteness is necessary).**

$$\neg EventuallyEntersPeriodicCore(succ, 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FunctionalGraphs/FinitenessIsNotImmediateDegeneracy.finiteness_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The successor map on the concrete infinite carrier Nat has no periodic orbit point, so its orbit from zero never enters a periodic core.

**Theorem 1.3 (Finiteness is not immediate degeneracy).**

$$(\forall Y, Finite(Y) \Rightarrow \forall \tau, y, EventuallyEntersPeriodicCore(\tau, y)) \land\\(\forall N \in \mathbb{N}, \exists Y, \tau, y, Fintype(Y) \land N < minimalPeriod(\tau, y)) \land\\(\forall N \in \mathbb{N}, \exists Y, \tau, y, ell, Fintype(Y) \land N < ell \land HasTransientLength(\tau, y, ell)) \land\\(\forall N \in \mathbb{N}, \exists Y, \tau, y, Fintype(Y) \land InitialOrbitInjective(\tau, y, N) \land EventuallyEntersPeriodicCore(\tau, y)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FunctionalGraphs/FinitenessIsNotImmediateDegeneracy.finiteness_is_not_immediate_degeneracy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every self-map of a finite carrier eventually enters the canonical periodic core. This clause directly reuses the repository's finite orbit periodicity theorem.

Cyclic ZMod translations give arbitrarily large exact minimal periods. Finite countdown maps give arbitrarily large exact transient lengths before reaching their unique periodic state.

For every fixed window, a sufficiently long cyclic translation has pairwise distinct states throughout that window despite already being periodic.

The Lean module separately checks empty and singleton carriers, constant and identity maps, exact transient length zero, and a zero-length initial window.

## References

- Truth anchor: `D5/S3/ObserverMemory/FunctionalGraphs/FinitenessIsNotImmediateDegeneracy.finiteness_is_necessary`
- Truth anchor: `D5/S3/ObserverMemory/FunctionalGraphs/FinitenessIsNotImmediateDegeneracy.finiteness_is_not_immediate_degeneracy`
- Truth anchor: `D5/S3/ObserverMemory/FunctionalGraphs/FinitenessIsNotImmediateDegeneracy.periodic_structure_does_not_determine_readout_richness`
- Dependency: [D5/S3/ObserverMemory/FunctionalGraphs/FiniteFunctionalGraphFittingDecomposition](FiniteFunctionalGraphFittingDecomposition.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound](../Prediction/FiniteOrbitPeriodBound.md)
