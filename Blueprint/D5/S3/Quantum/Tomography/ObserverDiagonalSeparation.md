# Observer Diagonal Separation

## Abstract

An information-complete quantum readout coexists with diagonal escape.

**Definition 1.1 (Projector-trace context readout).**

$$\forall n: Nat, context: \operatorname{Fin}(n+2) \to \operatorname{RankOneContext}\left(n+1\right), rho: \operatorname{Matrix}\left(\operatorname{Fin}(n+1), \operatorname{Fin}(n+1), Complex\right),\\{}\operatorname{contextReadout}\left(context, rho\right) = \operatorname{fun}\left(l, j,  , \operatorname{trace}\left(\operatorname{mul}\left(rho, \operatorname{projector}\left(context, l, j\right)\right)\right)\right).$$

*Formalization.* `D5/S3/Quantum/Tomography/ObserverDiagonalSeparation.contextReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout is built directly from the canonical rank-one context carrier: each coordinate is the complex trace of the state matrix times the named context projector.

**Theorem 1.2 (Empirical observer and diagonal separation).**

$$\exists context: \operatorname{Fin}(2) \to \operatorname{RankOneContext}\left(1\right),\\{}{\forall l, k, j, r, \operatorname{trace}\left(\operatorname{mul}\left(\operatorname{projector}\left(context, l, j\right), \operatorname{projector}\left(context, k, r\right)\right)\right) = \operatorname{if}\left(\operatorname{Eq}\left(l, k\right), \operatorname{if}\left(\operatorname{Eq}\left(j, r\right), 1, 0\right), \operatorname{inverse}\left(1\right)\right)} \land \operatorname{Injective}\left(\operatorname{contextReadout}\left(context\right)\right) \land \exists evaluation: Unit \to \left(Unit \to Bool\right), \exists twist: Bool \to Bool,\\{}{\forall y, \operatorname{Neq}\left(\operatorname{twist}\left(y\right), y\right)} \land \operatorname{fun}\left(a,  , \operatorname{twist}\left(\operatorname{evaluation}\left(a, a\right)\right)\right) \neg \in \operatorname{range}\left(evaluation\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/ObserverDiagonalSeparation.empirical_observer_diagonal_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness uses the repository's exact rank-one context and matrix carrier. Complementary overlaps are public, and the resulting projector-trace readout is injective on all one-dimensional complex matrices by the imported tomography theorem.

Independently, a Unit-indexed Boolean evaluation list and a Boolean fixed-point-free twist satisfy the public diagonal non-capture clause by the imported Lawvere escape theorem.

Search found both exact supporting declarations but no combined existential; the two carriers and all hypotheses remain explicit in the statement.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/ObserverDiagonalSeparation.contextReadout`
- Truth anchor: `D5/S3/Quantum/Tomography/ObserverDiagonalSeparation.empirical_observer_diagonal_separation`
- Dependency: [D5/S0/Diagonal/Lawvere/QualitativeEscape](../../../S0/Diagonal/Lawvere/QualitativeEscape.md)
- Dependency: [D5/S3/Quantum/Tomography/CompleteContextTomography](CompleteContextTomography.md)
