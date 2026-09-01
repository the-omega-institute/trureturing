# Three Closure Nonimplications

## Abstract

Prediction, operational, classical-answer, and self-description closure are separated by three concrete observer constructions.

**Theorem 1.1 (Prediction, operation, classical answers, and self-description separate).**

$$\left(\operatorname{predictionStableAt}\left((x \mapsto x - 1), (x \mapsto unit), 0\right) \land \operatorname{AlgebraAdjoin}\left(Complex, \operatorname{pair}\left(\operatorname{deterministicProjection}\left((x \mapsto unit), unit\right), \operatorname{shiftMatrix}\left(2\right)\right)\right) \ne \operatorname{top}\left(\operatorname{Matrix}\left(\operatorname{ZMod}\left(2\right), \operatorname{ZMod}\left(2\right), Complex\right)\right)\right) \land \left(\left(\operatorname{windowGeneratedAlgebra}\left(2\right) = \operatorname{top}\left(\operatorname{Matrix}\left(\operatorname{ZMod}\left(2\right), \operatorname{ZMod}\left(2\right), Complex\right)\right) \land \operatorname{IsEmpty}\left(\operatorname{ComplexAlgHom}\left(\operatorname{windowGeneratedAlgebra}\left(2\right), Complex\right)\right)\right) \land \left(\exists context \in \operatorname{Fin}\left(2\right) \to \operatorname{RankOneContext}\left(1\right),\; \operatorname{Injective}\left(\operatorname{contextReadout}\left(context\right)\right) \land \left(\exists evaluation \in \operatorname{Matrix}\left(\operatorname{Fin}\left(1\right), \operatorname{Fin}\left(1\right), Complex\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(1\right), \operatorname{Fin}\left(1\right), Complex\right) \to Bool\right), twist \in Bool \to Bool,\; \left(\forall y \in Bool,\; \operatorname{twist}\left(y\right) \ne y\right) \land \left(\neg (a \mapsto \operatorname{twist}\left(\operatorname{evaluation}\left(a, a\right)\right)) \in \operatorname{range}\left(evaluation\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/ClosureNonimplicationTriple.closure_nonimplication_triple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the two-address cyclic carrier, the constant Unit readout is prediction-stable at depth zero. Its deterministic readout projection together with the cyclic shift generates a proper subalgebra: every generator commutes with the shift, whereas the frozen clock-shift commutator is nonzero.

The second countermodel applies the frozen nontrivial-window theorem: the canonical clock and shift generate the full matrix algebra, but that generated algebra has no unital complex character.

The third countermodel applies the frozen rank-one-context theorem. Its projector-trace readout is injective on the complete matrix carrier, while a Boolean evaluator indexed twice by that same carrier and a fixed-point-free twist exhibit an escaped diagonal.

Repository search found the three exact component owners but no whole-statement owner. Pinned Mathlib supplied only the generic commutation lemma for elements of a generated algebra.

## References

- Truth anchor: `D5/S3/Observer/Completion/ClosureNonimplicationTriple.closure_nonimplication_triple`
- Dependency: [D5/S3/Observer/WindowAlgebra/OperationalClassicalSeparation](../WindowAlgebra/OperationalClassicalSeparation.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ConditionalEntropyStability](../../ObserverMemory/Prediction/ConditionalEntropyStability.md)
- Dependency: [D5/S3/Quantum/Algebra/CovariantCommutator](../../Quantum/Algebra/CovariantCommutator.md)
- Dependency: [D5/S3/Quantum/Measurements/DeterministicReadoutPvm](../../Quantum/Measurements/DeterministicReadoutPvm.md)
- Dependency: [D5/S3/Quantum/Tomography/ObserverDiagonalSeparation](../../Quantum/Tomography/ObserverDiagonalSeparation.md)
