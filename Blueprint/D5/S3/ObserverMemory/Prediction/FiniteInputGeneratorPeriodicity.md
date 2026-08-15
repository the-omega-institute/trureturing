# Finite Input Generator Periodicity

## Abstract

A finite deterministic input generator makes every extended orbit eventually periodic.

**Theorem 1.1 (Finite input generators give eventually periodic product orbits).**

$$\forall Y, C, U,\ [\operatorname{Finite}(Y)] [\operatorname{Finite}(C)],\ F: U \to Y \to Y, J: C \to C, g: C \to U,\ \forall z_{0}\in Y\times C,\ \exists mu, p\in \mathbb{N},\ 0 < p \land \forall t\in \mathbb{N},\ ((y, c) \mapsto (F(g(c))(y), J(c)))^{mu+t+p}(z_{0}) = ((y, c) \mapsto (F(g(c))(y), J(c)))^{mu+t}(z_{0}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteInputGeneratorPeriodicity.finite_input_generator_eventually_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a finite state carrier and C a finite deterministic input generator with transition J and output g into the input type U. For an input-indexed update F, the displayed self-map sends (y,c) to (F(g(c))(y),J(c)) on Y times C.

For every initial product state there are a tail index mu and a strictly positive period p such that all iterates after mu agree when shifted by p. This is the eventual periodicity of the whole extended trajectory, not merely a repeated pair of states.

The exact pinned-library hit Finite.exists_ne_map_eq_of_infinite gives two equal states in the orbit map from the naturals to the finite product carrier and is imported and applied. Loogle also found EquivFin.not_injective_infinite_finite. LeanSearch returned the nearby injective-map periodic-points lemma, which does not apply to arbitrary updates, and no exact theorem. Repository and formalization searches found no duplicate.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteInputGeneratorPeriodicity.finite_input_generator_eventually_periodic`
