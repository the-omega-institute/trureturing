# Ordinary grid and cylinder domination growth

## Abstract

Ordinary grid and cylinder domination growth

**Definition 1.1 (Actual labelled subsets).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth.count`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth.count` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count is the cardinality of the existing ordinary dominating-set family domSets. Every distinct subset is counted once, including nonminimal subsets; no symmetry quotient is taken. The grid and cylinder use Mathlib pathGraph, cycleGraph and Cartesian graph product on Fin m times Fin n. Thus the source domination polynomial at z=1 is exactly this count.

**Definition 1.2 (Complete joint target).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth.JointGrowth`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth.JointGrowth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The target has one existential real mu in [1,2]. For every positive epsilon one natural N at least three works for both actual counts and every pair m,n at least N. No aspect ratio is bounded. The function growth a m n is the real power a raised to one divided by the natural product m*n.

**Theorem 1.3 (Finite seam repair).**

$$\forall (m:\mathbb{N}), \forall (n:\mathbb{N}), (3 \le m) \Rightarrow ((\operatorname{count}\left(\operatorname{grid}\left(m, n\right)\right) \le \operatorname{count}\left(\operatorname{cylinder}\left(m, n\right)\right)) \land (\operatorname{count}\left(\operatorname{cylinder}\left(m, n\right)\right) \le \operatorname{count}\left(\operatorname{grid}\left(m, n\right)\right) \cdot 4^{n}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth.finite_seam_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least three and every natural n, g(m,n) is at most c(m,n), which is at most g(m,n) times 4 to the power n. The lower inequality uses pathGraph_le_cycleGraph. The upper inequality fills both endpoint columns. The pair of the repaired grid subset and the original boundary intersection determines the cylinder subset, giving an injection into the grid family times the boundary powerset. The boundary has exactly 2n vertices. The proof includes m=3 and n=1, and additionally allows n=0 in this finite lemma.

**Theorem 1.4 (Block choices and selected padding).**

$$\forall (a:\mathbb{N}), \forall (b:\mathbb{N}), \forall (M:\mathbb{N}), \forall (N:\mathbb{N}), \operatorname{count}\left(\operatorname{grid}\left(a, b\right)\right)^{\operatorname{quotient}\left(M, a\right) \cdot \operatorname{quotient}\left(N, b\right)} \le \operatorname{count}\left(\operatorname{grid}\left(M, N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth.tiling_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural a,b,M,N, disjoint translated a-by-b blocks inject independent dominating-subset choices into the M-by-N grid. All leftover vertices are selected. Restriction to each embedded block recovers its original choice. The generic block_count proof permits additional cross-block edges and requires no independence of the resulting graph. The number of blocks is the product of the natural quotients M/a and N/b (quotient denotes Nat.div in the displayed formula); zero-sized blocks cause no unproved cutoff.

**Theorem 1.5 (Equal unrestricted joint limits).**

$$\exists (mu:\mathbb{R}), ((1 \le mu) \land (mu \le 2)) \land (\forall (epsilon:\mathbb{R}), (0 < epsilon) \Rightarrow (\exists (N:\mathbb{N}), (3 \le N) \land (\forall (m:\mathbb{N}), \forall (n:\mathbb{N}), (N \le m) \Rightarrow ((N \le n) \Rightarrow ((\left|\operatorname{growth}\left(\operatorname{count}\left(\operatorname{grid}\left(m, n\right)\right), m, n\right) - mu\right| < epsilon) \land (\left|\operatorname{growth}\left(\operatorname{count}\left(\operatorname{cylinder}\left(m, n\right)\right), m, n\right) - mu\right| < epsilon))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth.result` (`✓ std3`). ∎

*Resolves.* `Problems/mertens-2024-grid-cylinder-joint-growth` (proved) by `D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mertens-2024-grid-cylinder-joint-growth","declaration_gid":"D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Let L be the supremum of log g(a,b)/(ab), with zero-area rates defined by division by zero as zero, and let mu=exp L. The all-vertex subset and powerset bound give 0<=L<=log 2. For each fixed positive block, the tiling inequality gives its normalized log rate times the two covered proportions as a lower bound on every large grid rate. Each covered proportion tends to one because the uncovered remainder divided by the side length tends to zero. A supremum argument therefore gives the joint grid limit L. The finite seam inequality puts the cylinder log rate between the grid log rate and that rate plus log 4 divided by m, uniformly in n. Joint squeezing gives the same L. Continuity of exp yields the required real-power limits with one common N for all sufficiently large m,n.

Source: Stephan Mertens, Journal of Integer Sequences 27 (2024), Article 24.7.6, definitions on pp. 1–2, joint growth discussion (15)–(17), and the conjecture after (22) on p. 19. The journal and arXiv v1 have different pagination. The argument proves grid-limit existence and does not assume it. It establishes neither a numerical value of mu nor a convergence rate for the grid itself. No worldwide openness or priority claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth.JointGrowth`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth.count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth.finite_seam_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth.tiling_count`
- Dependency: [D5/S3/Combinatorics/Graph/DominatingSetAverage](../DominatingSetAverage.md)
