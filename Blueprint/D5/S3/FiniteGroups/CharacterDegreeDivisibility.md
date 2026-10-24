# Character Degree Divisibility

## Abstract

Finite representation theory relates simple modules, characters, conjugation and induction.

**Theorem 1.1 (Trace eq finrank iff).**

$$\forall V \in Type*,\; [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(\operatorname{Complex}, V\right)], [\operatorname{FiniteDimensional}\left(\operatorname{Complex}, V\right)], \forall f \in \operatorname{Module}.\operatorname{End}\left(\operatorname{Complex}, V\right),\; \forall n \in \operatorname{Nat},\; (\operatorname{Ne}\left(n, 0\right)) \Rightarrow (((\operatorname{HPow}.\operatorname{hPow}\left(f, n\right)) = (1)) \Rightarrow (((\operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{LinearMap}.\operatorname{trace}\left(\operatorname{Complex}, V\right), f\right)) = (\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Module}.\operatorname{finrank}\left(\operatorname{Complex}, V\right)\right))) \Leftrightarrow ((f) = (1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CharacterDegreeDivisibility.trace_eq_finrank_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

**Theorem 1.2 (Finrank dvd card).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [\operatorname{Field}\left(k\right)], [\operatorname{Group}\left(G\right)], [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(k, V\right)], [\operatorname{Finite}\left(G\right)], [\operatorname{IsAlgClosed}\left(k\right)], [\operatorname{CharZero}\left(k\right)], [\operatorname{FiniteDimensional}\left(k, V\right)], \forall rho \in \operatorname{Representation}\left(k, G, V\right),\; [\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right)], \operatorname{Dvd}.\operatorname{dvd}\left(\operatorname{Module}.\operatorname{finrank}\left(k, V\right), \operatorname{Nat}.\operatorname{card}\left(G\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CharacterDegreeDivisibility.finrank_dvd_card` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Claude (2026). *TauCeti finite representation and character theory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5>.

*Commentary.*

The displayed conclusion holds under the stated hypotheses.

## References

- Truth anchor: `D5/S3/FiniteGroups/CharacterDegreeDivisibility.finrank_dvd_card`
- Truth anchor: `D5/S3/FiniteGroups/CharacterDegreeDivisibility.trace_eq_finrank_iff`
- Dependency: [D5/S3/FiniteGroups/FiniteCharacterAlgebra](FiniteCharacterAlgebra.md)
