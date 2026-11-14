# Finite observations and global effect probabilities

## Abstract

Finite Born readouts admit normalized Borel responses with maximal global deviations.

Work in the complex matrices indexed by Fin d, with d at least one. An effect E satisfies positivity of E and of I minus E. A density is positive semidefinite with complex trace exactly one. The matrix space carries its usual finite product topology and Borel sigma algebra; I and zero denote the identity and zero matrices, and val forgets the effect subtype.

**Theorem 1.1 (Exact finite agreement with maximal global deviations).**

$$\forall (d: \mathbb{N}), ((1 \leq d) \implies (\forall (T: \operatorname{Finset}(\{X: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}) \mid (\operatorname{PosSemidef}(X)) \land (\operatorname{PosSemidef}((I_{d}-X)))\})), (\forall (\rho_{*}: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), (((\operatorname{PosSemidef}(\rho_{*})) \land (\operatorname{Tr}(\rho_{*}) = 1)) \implies (\exists (p: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}) \to \mathbb{R}), ((\operatorname{Measurable}(p)) \land (\forall (E: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((I_{d}-E)))) \implies ((0 \leq p(E)) \land (p(E) \leq 1)))) \land (p(0_{d}) = 0) \land (p(I_{d}) = 1) \land (\forall (E: \{X: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}) \mid (\operatorname{PosSemidef}(X)) \land (\operatorname{PosSemidef}((I_{d}-X)))\}), ((E \in T) \implies (p(\operatorname{val}(E)) = \Re \operatorname{Tr}(\rho_{*} \operatorname{val}(E))))) \land (\forall (E: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), (\forall (F: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}(F)) \land (\operatorname{PosSemidef}((I_{d}-(E+F))))) \implies (\lvert ((p((E+F))-p(E))-p(F)) \rvert  \leq 2)))) \land (\exists (E: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), (\exists (F: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), ((E \neq F) \land ((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}(F)) \land (\operatorname{PosSemidef}((I_{d}-(E+F))))) \land (\lvert ((p((E+F))-p(E))-p(F)) \rvert  = 2)))) \land (\forall (\rho: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), (((\operatorname{PosSemidef}(\rho)) \land (\operatorname{Tr}(\rho) = 1)) \implies ((\forall (E: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((I_{d}-E)))) \implies (\lvert (p(E)-\Re \operatorname{Tr}(\rho E)) \rvert  \leq 1))) \land (\forall (eta: \mathbb{R}), ((0 < eta) \implies (\exists (E: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((I_{d}-E)))) \land ((1-eta) < \lvert (p(E)-\Re \operatorname{Tr}(\rho E)) \rvert ))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectFiniteObservationCountermodel.finite_observation_countermodel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any finite set T of actual effects and any reference density. A positive a with three times a below one can be chosen so that every positive scalar effect tI with t at most three times a misses T. A finite induction uses one diagonal entry: a positive entry bounds a smaller gap, while a nonpositive entry cannot equal a positive scalar matrix.

Set the response to one at 2aI and at aI divided by (n plus one) for every natural n, to zero at 3aI, and to the reference Born trace elsewhere. These exceptional points miss T, zero and I. The high set is countable, so the total response is Borel measurable. Trace positivity bounds the reference probabilities between zero and one on every effect.

The distinct effects aI and 2aI sum to 3aI and attain binary defect two. The effect range bounds every admissible binary defect by two. Against any density, the scalar Born trace at aI divided by (n plus one) tends to zero while the response stays one. Thus every positive tolerance has a strict distance witness, and all effect distances are at most one.

The response depends on T. Finite readouts can identify a density inside the globally additive Born model, while these responses need not satisfy that model's global additivity hypothesis. Exact and approximate global additivity representation theorems retain their hypotheses. No physical realization follows from this construction.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/EffectFiniteObservationCountermodel.finite_observation_countermodel`
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation](../QuantumChannels/PositiveFilterTransposeRefutation.md)
