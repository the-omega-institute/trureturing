# Original finite-memory directed graphs

## Abstract

The original lower and upper finite-memory source languages are exactly the bilateral labels of a finite directed graph, whose retained paths have the original weighted adjacency expansion.

A vertex is a function from Fin n to the original c/u alphabet. Index zero holds the most recent past letter. Reversing these indices gives the chronological n-letter word. A transition inserts its label at index zero and drops the oldest letter. The seed composition uses the original high-side letter maps. A current run of K+1 c letters is forbidden. At the current Kth c, the lower graph requires a strict zero-seed bound; the upper graph requires a nonstrict h-seed bound. Both use the original threshold chi to K-1 times d.

**Theorem 1.1 (window value).**

$$\forall n \in Nat, omega \in Int \to CuLetter, i \in Int, z \in Real,\; \operatorname{memoryValue}\left(\operatorname{memoryWindow}\left(n, omega, i\right), z\right) = \operatorname{finitePast}\left(omega, i, n, z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.window_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The graph seed composition equals finitePast on the actual n-letter past, for every real seed and integer position.

**Theorem 1.2 (window shift).**

$$\forall n \in Nat, omega \in Int \to CuLetter, i \in Int,\; \operatorname{memoryWindow}\left(n, omega, \operatorname{add}\left(i, 1\right)\right) = \operatorname{memoryShift}\left(\operatorname{memoryWindow}\left(n, omega, i\right), \operatorname{apply}\left(omega, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.window_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Moving one integer position inserts exactly the current letter into the past window.

**Theorem 1.3 (path memory reconstruction).**

$$\forall n \in Nat, p \in Int \to \operatorname{MemoryVertex}\left(n\right), omega \in Int \to CuLetter,\; \left(\forall i \in Int,\; \operatorname{apply}\left(p, \operatorname{add}\left(i, 1\right)\right) = \operatorname{memoryShift}\left(\operatorname{apply}\left(p, i\right), \operatorname{apply}\left(omega, i\right)\right)\right) \Rightarrow p = \operatorname{memoryWindow}\left(n, omega\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.path_memory_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on each finite memory coordinate reconstructs it from the bilateral label sequence. No arbitrary memory annotation survives the shift equations.

**Theorem 1.4 (window run).**

$$\forall n \in Nat, r \in Nat, omega \in Int \to CuLetter, i \in Int,\; \left(\operatorname{lt}\left(0, r\right) \land \operatorname{le}\left(r, \operatorname{add}\left(n, 1\right)\right)\right) \Rightarrow \left(\operatorname{memoryRun}\left(\operatorname{memoryWindow}\left(n, omega, i\right), \operatorname{apply}\left(omega, i\right), r\right) \Leftrightarrow \left(\forall k \in \operatorname{Fin}\left(r\right),\; \operatorname{apply}\left(omega, \operatorname{subtract}\left(i, \operatorname{toInt}\left(k\right)\right)\right) = c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.window_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive run lengths up to n+1, the finite memory test is exactly the run ending at the current position, including the current letter.

**Theorem 1.5 (forbidden run reversal).**

$$\forall K \in Nat, omega \in Int \to CuLetter,\; \left(\forall i \in Int,\; \operatorname{not}\left(\forall k \in \operatorname{Fin}\left(\operatorname{add}\left(K, 1\right)\right),\; \operatorname{apply}\left(omega, \operatorname{add}\left(i, \operatorname{toInt}\left(k\right)\right)\right) = c\right)\right) \Leftrightarrow \left(\forall i \in Int,\; \operatorname{not}\left(\forall k \in \operatorname{Fin}\left(\operatorname{add}\left(K, 1\right)\right),\; \operatorname{apply}\left(omega, \operatorname{subtract}\left(i, \operatorname{toInt}\left(k\right)\right)\right) = c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.forbidden_run_reversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversing the K+1 indices converts the original forward forbidden block into the equivalent current-ending block without changing the sequence.

**Theorem 1.6 (original memory graph correspondence).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \forall omega \in Int \to CuLetter,\; \left(\operatorname{lt}\left(0, K\right) \land \operatorname{le}\left(K, n\right)\right) \Rightarrow \left(\operatorname{member}\left(omega, \operatorname{MemoryLanguage}\left(side, n, K, d\right)\right) \Leftrightarrow \operatorname{existsUnique}\left(\left(\operatorname{BilateralGraphPath}\left(side, K, d, p, omega\right)\right)_{p \in Int \to \operatorname{MemoryVertex}\left(n\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.original_memory_graph_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least K and positive K, each original lower or upper sequence has exactly one bilateral graph path. Conversely every graph path has the reconstructed actual past windows and precisely the original guard at the current Kth c. All thresholds d remain in scope.

**Theorem 1.7 (prepend bilateral path).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \forall v \in \operatorname{MemoryVertex}\left(n\right), t \in \operatorname{MemoryVertex}\left(n\right), a \in CuLetter, p \in Int \to \operatorname{MemoryVertex}\left(n\right), omega \in Int \to CuLetter,\; \left(\operatorname{LiveVertex}\left(side, K, d, v\right) \land \left(\operatorname{BilateralGraphPath}\left(side, K, d, p, omega\right) \land \left(\operatorname{apply}\left(p, 0\right) = t \land \operatorname{MemoryEdge}\left(side, K, d, v, a, t\right)\right)\right)\right) \Rightarrow \left(\exists q \in Int \to \operatorname{MemoryVertex}\left(n\right), nu \in Int \to CuLetter,\; \operatorname{BilateralGraphPath}\left(side, K, d, q, nu\right) \land \left(\operatorname{apply}\left(q, 0\right) = v \land \left(\operatorname{apply}\left(nu, 0\right) = a \land \left(\forall i \in Int,\; \operatorname{le}\left(0, i\right) \Rightarrow \operatorname{apply}\left(nu, \operatorname{add}\left(i, 1\right)\right) = \operatorname{apply}\left(omega, i\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.prepend_bilateral_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A retained start supplies a genuine left past. One allowed edge joins it to a genuine right future at the edge target. The joined path preserves the selected label and every future letter.

**Theorem 1.8 (retained walk extension).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \forall v \in \operatorname{MemoryVertex}\left(n\right), w \in \operatorname{List}\left(CuLetter\right),\; \operatorname{RetainedWalk}\left(side, K, d, v, w\right) \Rightarrow \left(\exists p \in Int \to \operatorname{MemoryVertex}\left(n\right), omega \in Int \to CuLetter,\; \operatorname{BilateralGraphPath}\left(side, K, d, p, omega\right) \land \left(\operatorname{apply}\left(p, 0\right) = v \land \left(\forall k \in \operatorname{Fin}\left(\operatorname{length}\left(w\right)\right),\; \operatorname{apply}\left(omega, \operatorname{toInt}\left(k\right)\right) = \operatorname{getElem}\left(w, k\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.retained_walk_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite path through retained vertices has an actual two-sided extension. Induction joins one edge at a time and preserves every finite word letter. Empty paths and transient bridges are included; strong connectivity is unnecessary.

**Theorem 1.9 (bilateral path segment).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \forall p \in Int \to \operatorname{MemoryVertex}\left(n\right), omega \in Int \to CuLetter, w \in \operatorname{List}\left(CuLetter\right), i \in Int,\; \left(\operatorname{BilateralGraphPath}\left(side, K, d, p, omega\right) \land \left(\forall k \in \operatorname{Fin}\left(\operatorname{length}\left(w\right)\right),\; \operatorname{apply}\left(omega, \operatorname{add}\left(i, \operatorname{toInt}\left(k\right)\right)\right) = \operatorname{getElem}\left(w, k\right)\right)\right) \Rightarrow \operatorname{RetainedWalk}\left(side, K, d, \operatorname{apply}\left(p, i\right), w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.bilateral_path_segment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any finite word occurring on one bilateral path gives a retained walk starting at its actual vertex. Translation supplies the required bilateral realization of each visited vertex.

**Theorem 1.10 (original weighted path count).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \forall T \in Nat,\; \left(\operatorname{lt}\left(0, K\right) \land \operatorname{le}\left(K, n\right)\right) \Rightarrow \left(\operatorname{Finite}\left(\operatorname{RetainedPathDictionary}\left(side, n, K, d, T\right)\right) \land \left(\operatorname{le}\left(\operatorname{factorCount}\left(\operatorname{MemoryLanguage}\left(side, n, K, d\right), T\right), \operatorname{NatCard}\left(\operatorname{RetainedPathDictionary}\left(side, n, K, d, T\right)\right)\right) \land \operatorname{le}\left(\operatorname{NatCard}\left(\operatorname{RetainedPathDictionary}\left(side, n, K, d, T\right)\right), \operatorname{multiply}\left(\operatorname{power}\left(2, n\right), \operatorname{factorCount}\left(\operatorname{MemoryLanguage}\left(side, n, K, d\right), T\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.original_weighted_path_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every total weight T, the complete retained path dictionary is finite. Forgetting the initial vertex maps onto the original factor dictionary. A path is determined by its word and initial n-letter vertex, so its count is between the factor count and 2 to n times that count. Weight zero and unsupported weights retain the same formulas.

**Theorem 1.11 (original weighted adjacency paths).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \forall z \in Real,\; \left(\forall k \in Nat, v \in \operatorname{CoreVertex}\left(side, n, K, d\right), choices \in \operatorname{Fin}\left(k\right) \to \operatorname{Product}\left(CuLetter, \operatorname{CoreVertex}\left(side, n, K, d\right)\right),\; \operatorname{CorePath}\left(side, K, d, k, v, choices\right) \Rightarrow \operatorname{RetainedWalk}\left(side, K, d, \operatorname{val}\left(v\right), \operatorname{ofFn}\left(\left(\operatorname{fst}\left(\operatorname{apply}\left(choices, i\right)\right)\right)_{i \in \operatorname{Fin}\left(k\right)}\right)\right)\right) \land \left(\forall k \in Nat, v \in \operatorname{CoreVertex}\left(side, n, K, d\right),\; \operatorname{sum}\left(\left(\operatorname{matrixEntry}\left(\operatorname{power}\left(\operatorname{weightedAdjacency}\left(side, n, K, d, z\right), k\right), v, t\right)\right)_{t \in \operatorname{CoreVertex}\left(side, n, K, d\right)}\right) = \operatorname{sum}\left(\left(\operatorname{coreMonomial}\left(side, K, d, z, k, v, choices\right)\right)_{choices \in \operatorname{Fin}\left(k\right) \to \operatorname{Product}\left(CuLetter, \operatorname{CoreVertex}\left(side, n, K, d\right)\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.original_weighted_adjacency_paths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix is indexed by precisely the vertices appearing on bilateral paths. Its entry sums z to letterWeight(a) over all original allowed labels with those endpoints, including parallel labels. Each complete labeled path contributes z to its total original wordWeight; a disallowed path contributes zero. Matrix powers sum these monomials exactly. The empty path contributes one. Every allowed path supplies a retained word in the same graph, which has a two-sided extension by the preceding theorem. Identifying the convergence boundary with a unique spectral-radius-one root, and then identifying that root with the weighted factor rate, are separate conclusions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.bilateral_path_segment`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.forbidden_run_reversal`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.original_memory_graph_correspondence`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.original_weighted_adjacency_paths`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.original_weighted_path_count`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.path_memory_reconstruction`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.prepend_bilateral_path`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.retained_walk_extension`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.window_run`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.window_shift`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.window_value`
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors](ResetFactors.md)
