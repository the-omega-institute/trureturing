# Native sparse-paving matching obstruction

## Abstract

A specified basis fails exactly when its admissible target union is a circuit-hyperplane.

**Definition 1.1 (admissibleUnion).**

$$\forall (G: Type), [AddCommGroup\left(G\right)] \forall (A: Set\left(G\right)), \forall (B: Set\left(G\right)), \forall (X: Set\left(G\right)), \forall (b: G), (b \in admissibleUnion\left(A, B, X\right)) \Leftrightarrow ((b \in B) \land (\exists (s: G), (s \in X) \land (\neg(s + b \in A))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/SparsePavingMatchingObstruction.admissibleUnion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The admissible targets are the union over the specified source set: a target belongs if at least one source element has its sum outside the source ground. The empty source set gives the empty union. Its complement in the target ground is the set of translations keeping every source element inside the source ground.

**Definition 1.2 (BasisMatches).**

$$\forall (G: Type), [AddCommGroup\left(G\right)] \forall (A: Set\left(G\right)), \forall (N: Matroid\left(G\right)), \forall (S: Set\left(G\right)), (BasisMatches\left(A, N, S\right)) \Leftrightarrow (\exists (T: Set\left(G\right)), (\operatorname{N}.\operatorname{IsBase}\left(T\right)) \land (\exists (f: Equiv\left(S, T\right)), \forall (s: S), \neg(s + f\left(s\right) \in A)))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/SparsePavingMatchingObstruction.BasisMatches` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The target-base existential ranges over all actual bases of the independently specified native target matroid. An equivalence of subtypes is a bijection between the source set and that target base. No representation, common ground, ordering, sign condition, or translation invariance of independence is required.

**Theorem 1.3 (basiswise_obstruction).**

$$\forall (G: Type), [AddCommGroup\left(G\right)] [IsAddTorsionFree\left(G\right)] \forall (M: Matroid\left(G\right)), \forall (N: Matroid\left(G\right)), [\operatorname{M}.\operatorname{Finite}] [\operatorname{N}.\operatorname{Finite}] [\operatorname{M}.\operatorname{Loopless}] [\operatorname{N}.\operatorname{Loopless}] \forall (r: \mathbb{N}), \forall (m: \mathbb{N}), (1 \le r) \Rightarrow ((\operatorname{M}.\operatorname{eRank} = r) \Rightarrow ((\operatorname{N}.\operatorname{eRank} = r) \Rightarrow ((IsSparsePaving\left(N\right)) \Rightarrow ((\neg(0 \in \operatorname{N}.\operatorname{E})) \Rightarrow ((\operatorname{Set}.\operatorname{ncard}\left(\operatorname{M}.\operatorname{E}\right) = m) \Rightarrow ((\operatorname{Set}.\operatorname{ncard}\left(\operatorname{N}.\operatorname{E}\right) = m) \Rightarrow (\forall (S: Set\left(G\right)), (\operatorname{M}.\operatorname{IsBase}\left(S\right)) \Rightarrow (((\neg(BasisMatches\left(\operatorname{M}.\operatorname{E}, N, S\right))) \Leftrightarrow ((\operatorname{N}.\operatorname{IsCircuit}\left(admissibleUnion\left(\operatorname{M}.\operatorname{E}, \operatorname{N}.\operatorname{E}, S\right)\right)) \land ((\operatorname{N}.\operatorname{IsFlat}\left(admissibleUnion\left(\operatorname{M}.\operatorname{E}, \operatorname{N}.\operatorname{E}, S\right)\right)) \land ((\operatorname{N}.\operatorname{eRk}\left(admissibleUnion\left(\operatorname{M}.\operatorname{E}, \operatorname{N}.\operatorname{E}, S\right)\right) + 1 = r) \land (\operatorname{Set}.\operatorname{ncard}\left(admissibleUnion\left(\operatorname{M}.\operatorname{E}, \operatorname{N}.\operatorname{E}, S\right)\right) = r))))) \land ((\neg(BasisMatches\left(\operatorname{M}.\operatorname{E}, N, S\right))) \Rightarrow ((2 \le r) \land ((r + 1 \le m) \land ((\operatorname{Set}.\operatorname{ncard}\left(\operatorname{Set}.\operatorname{sdiff}\left(\operatorname{N}.\operatorname{E}, admissibleUnion\left(\operatorname{M}.\operatorname{E}, \operatorname{N}.\operatorname{E}, S\right)\right)\right) = m - r) \land (S + \operatorname{Set}.\operatorname{union}\left(\operatorname{Set}.\operatorname{sdiff}\left(\operatorname{N}.\operatorname{E}, admissibleUnion\left(\operatorname{M}.\operatorname{E}, \operatorname{N}.\operatorname{E}, S\right)\right), \operatorname{Set}.\operatorname{singleton}\left(0\right)\right) = \operatorname{M}.\operatorname{E})))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SparsePavingMatchingObstruction.basiswise_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M and N be finite loopless native matroids on a torsion-free abelian group, of common positive rank r and equal ground cardinality m. Only N and its dual are required to be paving. The circuit and flat predicates, and the extended natural rank, are those of the actual N. The equation rho(C) + 1 = r states the hyperplane rank without truncated subtraction. All four consequences are conditional on failure, so rank one, full-rank grounds, and rank-zero duals remain within the quantified domain. Zero may belong to the source ground.

For each nonempty source subset X, the complement U of its admissible union satisfies X + (U union {0}) contained in the source ground. The pinned torsion-free Cauchy-Davenport theorem gives card(X) + card(U) at most m; zero contributes exactly once because it is excluded from the target ground. Subtracting from the target cardinality proves Hall's inequalities, including the empty-subset case separately.

Apply the pinned finite Hall theorem to obtain distinct admissible representatives. In a sparse-paving matroid, dual paving bounds every nonspanning set by r elements: otherwise its complementary set is smaller than the dual rank and is independent, contradicting the native dual-rank identity. Paving then identifies any dependent r-element representative image as a circuit and a flat. If an admissible target lies outside that image, replace the representative at an index admitting it. A circuit with one element deleted spans the same flat, so adjoining the outside target gives an independent r-element set and hence an actual base. Thus failure forces the entire admissible union to equal the circuit-hyperplane. The converse follows because a base-sized injective image inside that union would equal the dependent circuit.

Looplessness excludes a singleton circuit, giving r at least two. If m equals r, the rank equation contradicts the circuit-hyperplane condition. Complementary cardinalities give card(U) = m - r. Applying the same sumset estimate again makes the contained sumset have cardinality m, so it equals the source ground. The additive bound, dual-rank formula, and Hall theorem are reused library inputs; the native representative repair and their source-domain composition are the formalized inference. No claim of external novelty is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SparsePavingMatchingObstruction.BasisMatches`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SparsePavingMatchingObstruction.admissibleUnion`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SparsePavingMatchingObstruction.basiswise_obstruction`
- Dependency: [D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching](AliabadiZerbibMatroidMatching.md)
