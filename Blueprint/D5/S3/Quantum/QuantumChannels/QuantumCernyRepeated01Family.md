# A repeated 01 family of qubit synchronization obstructions

## Abstract

For every binary word of the form 01 u 01 z 1, with arbitrary binary words u and z, a dimension-three rank obstruction prevents it from being the unique shortest synchronizing word of two qubit channels.

**Definition 1.1 (Repeated 01 words).**

$$\forall u : \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right), \forall z : \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right), \operatorname{repeated01}\left(u, z\right) = \operatorname{List}.\operatorname{append}\left(\operatorname{List}.\operatorname{append}\left(\operatorname{List}.\operatorname{append}\left(\operatorname{List}.\operatorname{append}\left([0, 1], u\right), [0, 1]\right), z\right), [1]\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QuantumCernyRepeated01Family.repeated01` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

The two intervening words are arbitrary binary lists; the final 1 is fixed.

**Theorem 1.2 (A dimension-three rank obstruction).**

$$\forall K, V : \operatorname{Type}\left(\right), ((((\operatorname{Field}\left(K\right)) \land (\operatorname{AddCommGroup}\left(V\right))) \land (\operatorname{Module}\left(K, V\right))) \land (\operatorname{FiniteDimensional}\left(K, V\right))) \Rightarrow (\forall f : \operatorname{Fin}\left(2\right) \to \operatorname{End}\left(K, V\right), \forall u : \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right), \forall z : \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right), ((\operatorname{finrank}\left(K, V\right) \le 3) \land (\operatorname{wordComp}\left(f, \operatorname{repeated01}\left(u, z\right)\right) = 0)) \Rightarrow (((\operatorname{wordComp}\left(f, \operatorname{List}.\operatorname{append}\left(\operatorname{List}.\operatorname{append}\left([0, 1], u\right), [0, 1]\right)\right) = 0) \lor (\operatorname{wordComp}\left(f, \operatorname{List}.\operatorname{append}\left(\operatorname{List}.\operatorname{append}\left([0, 1], z\right), [1]\right)\right) = 0)) \lor ((\operatorname{wordComp}\left(f, \operatorname{List}.\operatorname{append}\left(\operatorname{List}.\operatorname{append}\left(\operatorname{List}.\operatorname{append}\left(\operatorname{List}.\operatorname{append}\left([1], u\right), [0, 1]\right), z\right), [1]\right)\right) = 0) \lor (\operatorname{wordComp}\left(f, \operatorname{List}.\operatorname{append}\left(\operatorname{List}.\operatorname{append}\left(\operatorname{List}.\operatorname{append}\left([0, 1], u\right), [0, 1]\right), z\right)\right) = 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QuantumCernyRepeated01Family.mortal_repeated01` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

If the family word has zero composite map, one of four structural words has zero composite map. Each is strictly shorter, independently of the two intervening lengths.

**Theorem 1.3 (No unique shortest qubit instance).**

$$\forall u : \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right), \forall z : \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right), \neg \operatorname{HasInstance}\left(2, \operatorname{repeated01}\left(u, z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QuantumCernyRepeated01Family.no_qubit_instance_repeated01` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

Differences of reachable qubit states span an invariant space of dimension at most three. Restriction turns synchronization into zero action on that space, and the rank obstruction supplies a different shorter synchronizing word.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyRepeated01Family.mortal_repeated01`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyRepeated01Family.no_qubit_instance_repeated01`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyRepeated01Family.repeated01`
- Dependency: [D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation](QuantumCernyThueMorseRefutation.md)
