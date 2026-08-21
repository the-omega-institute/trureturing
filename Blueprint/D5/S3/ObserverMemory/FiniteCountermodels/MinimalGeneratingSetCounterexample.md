# Minimal Generators Need Not Have One Cardinality

## Abstract

The Boolean square has deletion-minimal concept generators of cardinalities one and two.

**Theorem 1.1 (The Boolean square has differently sized minimal generators).**

$$\begin{gathered}X=\left\{0, 1\right\}^2,\\C_{1}((x_{1}, x_{2}))=(x_{1}, x_{2}), C_{2}((x_{1}, x_{2}))=x_{1}, C_{3}((x_{1}, x_{2}))=x_{2},\\Gen(\left\{C_{1}, C_{2}, C_{3}\right\}) \land Minimal(\left\{C_{1}\right\}) \land Minimal(\left\{C_{2}, C_{3}\right\}),\\card(\left\{C_{1}\right\})=1 \land card(\left\{C_{2}, C_{3}\right\})=2 \land 1 \neq 2.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FiniteCountermodels/MinimalGeneratingSetCounterexample.boolean_square_has_minimal_generators_of_sizes_one_and_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state carrier is the Boolean square. The identity concept returns the whole state, while the two coordinate concepts return the first and second bits. Their common sum codomain only makes the finite family homogeneous; equality of each readout has exactly the source meaning.

A family generates top_X when agreement on every member forces equality of states. A finite family is minimal when deleting any one member destroys that separation property. Thus the definition records genuine proper-subgenerator minimality rather than merely irredundancy by cardinality.

The identity singleton separates all states and its deletion does not. The two coordinates jointly separate states, while deleting either leaves one pair of states indistinguishable. The resulting finite certificates have cards one and two. Repository and pinned-library searches found no equal theorem.

## References

- Truth anchor: `D5/S3/ObserverMemory/FiniteCountermodels/MinimalGeneratingSetCounterexample.boolean_square_has_minimal_generators_of_sizes_one_and_two`
