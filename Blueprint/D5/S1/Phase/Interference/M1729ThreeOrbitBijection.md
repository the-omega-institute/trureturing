# 1729 Three-Orbit Bijection

## Abstract

The three prime factors of 1729 give exactly three singleton stationing choices.

**Theorem 1.1 (The three prime factors give three singleton choices).**

$$1729=7\cdot13\cdot19 \land \operatorname{Prime}(7) \land \operatorname{Prime}(13) \land \operatorname{Prime}(19) \land \operatorname{primeFactors}(1729)=\{7, 13, 19\} \land \operatorname{Nonempty}(\operatorname{Equiv}(\{S\subseteq\operatorname{primeFactors}(1729)\mid |S|=1\}, \operatorname{Fin}(3))).$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/M1729ThreeOrbitBijection.m1729_three_orbit_bijection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first conjunct is the exact factorization. The next three conjuncts certify primality, and the primeFactors equality says that no further prime factor occurs. The final Nonempty Equiv term is a checked bijection from singleton subsets of that exact factor set to Fin 3.

Pinned Mathlib supplies primeFactors_mul, the singleton prime-factor theorem, and equivFinOfCardEq. The existing three-singleton stationing theorem supplies the final cardinal count, so the declaration does not reprove it.

This is a deeper partial closure of the concrete 1729 clause only. The selector, member-table, direction, and prediction clauses in the same source atom are not asserted here.

## References

- Truth anchor: `D5/S1/Phase/Interference/M1729ThreeOrbitBijection.m1729_three_orbit_bijection`
- Dependency: [D5/S1/Phase/SeatTowerConsequences](../SeatTowerConsequences.md)
