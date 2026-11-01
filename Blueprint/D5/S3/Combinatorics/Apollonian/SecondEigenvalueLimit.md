# Second eigenvalue of the inner-face Apollonian stages

## Abstract

The exact all-natural-stage second ordinary-adjacency eigenvalue limit.

**Theorem 1.1 (The original limit along every natural stage).**

$$\lim_{n \to \infty, n \in \mathbb{N}} \frac{\operatorname{secondEigenvalue}(n)}{2^{n/2}} = \sqrt{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/SecondEigenvalueLimit.result` (`✓ std3`). ∎

*Resolves.* `Problems/radsarar-anando-2026-apollonian-second-eigenvalue` (proved) by `D5/S3/Combinatorics/Apollonian/SecondEigenvalueLimit.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"radsarar-anando-2026-apollonian-second-eigenvalue","declaration_gid":"D5/S3/Combinatorics/Apollonian/SecondEigenvalueLimit.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For the actual finite simple unweighted graph stages defined in InnerFaceStages, the second decreasing real eigenvalue of ordinary adjacency, counting characteristic-polynomial multiplicity, divided by the real power 2^((n:Real)/2), tends along all natural n to sqrt(2). Stage zero is the plane K4 with outer vertices a,b,c and centre o. Each successor inserts one vertex in every inner face, joins it to that face’s three corners, retains all old vertices and edges, and never subdivides the outer face. The theorem has no supplied degree, spectral, randomness or eventual-stage premise.

The proof formalizes the accepted ordinary argument linked in the source note. At every fixed cutoff k, the limiting Gram diagonal has central weight three, outer-corner weight two, and all remaining weights at most two. Its second decreasing eigenvalue is therefore two, including multiplicity. The compiled Gram convergence and Hermitian perturbation bound give convergence of the actual normalized second Gram eigenvalue to two and its eventual strict positivity. The unequal rectangular dilation identity then gives the normalized cutoff second eigenvalue tending to sqrt(2).

The actual cutoff equivalence transports the full ordinary adjacency spectrum without changing its order or multiplicity. The difference from the cutoff dilation is exactly the block diagonal formed from old adjacency and the actual late induced adjacency. Its Euclidean operator norm is at most the sum of their two norms. Real inclusion in the complex field preserves the ordered eigenvalues and the Hermitian operator norm, so the frozen complex perturbation theorem applies lawfully to the actual real matrices. The normalized late block is uniformly bounded by 3 sqrt(2)/2^(k/2), while the fixed old block tends to zero with the stage. First choosing k and then the later stage makes both errors and the cutoff spectral error small. This proves the limit on every sufficiently large natural stage, preserving odd stages through the original real-power normalization.

This is an application and formal completion of the accepted ordinary proof. It makes no literature-priority claim and does not treat source-page answer counts as mathematical evidence. Statements about other leading eigenvalues, normalized adjacency, Laplacians, random subdivisions and subdivision of the outer face are outside the theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Apollonian/SecondEigenvalueLimit.result`
- Dependency: [D5/S3/Combinatorics/Apollonian/CutoffGramLimit](CutoffGramLimit.md)
- Dependency: [D5/S3/Combinatorics/Apollonian/CutoffOrderedSpectrum](CutoffOrderedSpectrum.md)
