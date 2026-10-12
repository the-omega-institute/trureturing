# Reset codebook: Target

## Abstract

Reset codebooks, actual sources and weighted lower-memory graphs.

**Theorem 1.1 (original root exists unique).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookTarget.original_root_exists_unique`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookTarget.original_root_exists_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The mathlib community (2026). *Gelfand formula and the intermediate value theorem in mathlib*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d>.

*Commentary.*

For every K >= 2, n >= K and real guard threshold d, the original pruned 6/20 matrix has exactly one spectral root z in (0,1). Two low extensions from every retained vertex force its square at z=1 to have row sums at least two. Degree-6/20 comparisons give continuity and strict increase; the intermediate value theorem then gives the root.

**Definition 1.2 (RootFamily).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookTarget.RootFamily`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookTarget.RootFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by RootFamily(K : ℕ) (d : ℝ) := ∀ n : ℕ, K≤n → {z : ℝ // D5.S1.Digit.Infinite.ResetCodebook.Transfer.OriginalSpectralRoot K n d z}.

**Definition 1.3 (target6218).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookTarget.target6218`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookTarget.target6218` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the fixed complete codebook, let delta=B(M)-D0 and eps=chi^(K-1)*delta*g^N. The codebook is finite, both margins and the actual error margin are positive, and every finite actual reset list retains its literal source tails, color departures and bounded errors. Every bilateral auxiliary reset concatenation satisfies the cap, convergent finite-past state and all guarded-high lower bounds. One n>=K has h*rho^n<eps, contains every such auxiliary word in the original pruned graph, and has spectral gamma at least log2 of the full codebook cardinality divided by N+20+6M.

**Definition 1.4 (lowerRoot).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookTarget.lowerRoot`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookTarget.lowerRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by lowerRoot(K n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hKn : K ≤ n) : ℝ := (original_root_exists_unique K n d hK hKn).choose.

**Definition 1.5 (rootFamily).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookTarget.rootFamily`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookTarget.rootFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by rootFamily(K : ℕ) (d : ℝ) (hK : 2 ≤ K) : Statement.RootFamily K d := fun n hn => ⟨lowerRoot K n d hK hn,lowerRoot_spec K n d hK hn⟩.

**Theorem 1.6 (reset codebook common realization).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookTarget.reset_codebook_common_realization`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookTarget.reset_codebook_common_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The mathlib community (2026). *Gelfand formula and the intermediate value theorem in mathlib*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d>.

*Commentary.*

Fix either actual initial state, K >= 2, a reset length M >= 1, positive weight N, the strict budget window, the associated guard threshold and a nonempty complete weak codebook. All finite actual reset concatenations share a positive error margin and retain their literal high and low tails and every departure slot. Every bilateral auxiliary concatenation has the common strict high-state margin. One finite depth n >= K places all of them in the original lower graph, whose uniquely defined spectral gamma is at least log2 of the complete codebook cardinality divided by N+20+6M. Auxiliary bilateral sequences are distinct objects from the finite actual sources. This statement concerns the existence and uniqueness of the lower-graph root; the upper and lower graph rate equalities and nested monotonicity in 62.15 are separate statements.

## References

- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookTarget.RootFamily`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookTarget.lowerRoot`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookTarget.original_root_exists_unique`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookTarget.reset_codebook_common_realization`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookTarget.rootFamily`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookTarget.target6218`
- Dependency: [D5/S1/Digit/Infinite/ResetCodebookWeighted](ResetCodebookWeighted.md)
