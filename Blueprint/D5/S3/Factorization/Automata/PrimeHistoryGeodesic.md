# Shortest Prime History Representatives

## Abstract

Exact contextual behavior has a shortest three-run representative, with a matching all-word bound.

For a nonempty interval translation [l,u] with final displacement d in capacity a, the necessary visited displacement interval is [-l,a-u]. Every realizing history must account for both extrema. A word with the same net displacement but a smaller excursion would have a different legal starting-state set, and is not an admissible replacement.

**Theorem 1.1 (The lower bound is attained by an explicit word).**

$$\forall a \in \mathbb{N},\; \forall t \in IntervalMap\left(a\right),\; normal\left(a, shortestWord\left(t\right)\right) = some\left(t\right) \land \left((List.length\left(shortestWord\left(t\right)\right): \mathbb{Z}) = 2 \cdot \left((a: \mathbb{Z}) - t.hi + t.lo\right) - max\left(t.shift, -t.shift\right) \land \left(\forall w \in List\left(Bool\right),\; normal\left(a, w\right) = some\left(t\right) \Rightarrow List.length\left(shortestWord\left(t\right)\right) \le List.length\left(w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Automata/PrimeHistoryGeodesic.shortest_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative d, use the earlier lower-first realization. For negative d, reflect the capacity interval, realize the reflected form, then exchange multiplication and division. The proof computes its exact signature and length. Uniqueness of a nonempty normal form forces every competing word to have the same extrema and final displacement, so the all-word lower bound proves optimality. This is minimum operation count inside a contextual behavior class, not recovery of the original history's length and not a preservation theorem for other costs.

## References

- Truth anchor: `D5/S3/Factorization/Automata/PrimeHistoryGeodesic.shortest_realization`
- Dependency: [D5/S3/Factorization/Automata/PrimeHistoryNormalForm](PrimeHistoryNormalForm.md)
- Dependency: [D5/S3/Factorization/Automata/WordExcursionLowerBound](WordExcursionLowerBound.md)
