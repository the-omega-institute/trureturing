# Naive Refinement Complexity

## Abstract

Finite signature refinement has linear rounds and the stated sorting and hashing costs.

**Theorem 1.1 (Canonical refinement has the finite-system complexity bounds).**

$$\begin{gathered}\forall i, \operatorname{FiniteNonempty}(Y_{i}), \operatorname{FiniteNonempty}(O_{i}),\\{}n_{i} = \lvert Y_{i} \rvert,\\{}\tau_{i}: Y_{i} \to Y_{i}, q_{i}: Y_{i} \to O_{i}, \operatorname{Surjective}(q_{i}),\\{}s_{i} \in \operatorname{BigO}(n_{i}\log n_{i}), h_{i} \in \operatorname{BigO}(n_{i}), w_{i} \in \operatorname{BigO}(1) \longrightarrow\\{}(\operatorname{refinementRounds}(\tau_{i}, q_{i}) \leq n_{i}-\lvert O_{i} \rvert) \land\\{}(\operatorname{sortingRefinementWork}(\operatorname{refinementRounds}(\tau_{i}, q_{i}), s_{i}) \in \operatorname{BigO}(n_{i} \times {n_{i} - \lvert O_{i} \rvert + 1} \times \log n_{i})) \land\\{}(\operatorname{refinementWorkspace}(n_{i}, w_{i}) \in \operatorname{BigO}(n_{i})) \land\\{}(\operatorname{expectedHashRefinementWork}(\operatorname{refinementRounds}(\tau_{i}, q_{i}), h_{i}) \in \operatorname{BigO}(n_{i} \times {n_{i} - \lvert O_{i} \rvert + 1})).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/NaiveRefinementComplexity.naive_refinement_complexity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider a filter-indexed family of finite nonempty deterministic state systems. Each readout is surjective onto its realized output carrier. The algorithm recursively labels a state by its current readout and the preceding label of its successor, and stops at the first unchanged partition.

The sorting, hashing, and workspace assumptions concern independent one-round or one-state cost functions. Total sorting and expected hashing work are constructed by multiplying the corresponding round cost by the canonical number of rounds plus the initial labeling pass. Total workspace is constructed from one record per state.

The imported finite-stability theorem bounds the first unchanged partition by the state count minus the realized-output count. Mathlib's IsBigO.mul then composes that pointwise round bound with the primitive cost assumptions, producing the three displayed resource bounds.

Repository search directly found and applies controlled_finite_stability and its canonical stopping depth. Pinned Mathlib directly supplies IsBigO.mul, IsBigO.of_bound, and isBigO_refl. Loogle and LeanSearch executables were unavailable, and no single packaged theorem with all four clauses was found.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/NaiveRefinementComplexity.naive_refinement_complexity`
- Dependency: [D5/S3/ObserverMemory/Algorithms/ControlledFiniteStability](ControlledFiniteStability.md)
