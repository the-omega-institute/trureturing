# The fixed-resistance optimizer on the full labelled K2m family

## Abstract

The fixed-resistance Fiedler maximum on labelled K2m has exactly two edge restrictions.

The parameter m ranges over every natural number at least three. Vertices are Fin (2+m): the hubs are castAdd m 0 and castAdd m 1, and leaf i is natAdd 2 i. Only the two hub-to-leaf edges for each i are present. Every edge conductance varies independently over positive reals. The ordinary, unnormalized wLap, its nonzero mean-zero Rayleigh infimum lambda2, and the original harmonic-current totalRes are those of FiedlerResistanceInvariantWeightsRefutation. The total counts every unordered distinct vertex pair once, including nonedges. Feasible weights satisfy totalRes=R0 for an arbitrary R0>0; there is no total-conductance or competitor-symmetry constraint.

**Definition 1.1 (The labelled complete bipartite graph).**

$$\forall m \in \mathrm{Nat},\; \operatorname{K2m}\left(m\right) = \operatorname{SimpleGraph}.\operatorname{comap}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{finSumFinEquiv}\left(2, m\right)\right), \operatorname{completeBipartiteGraph}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(m\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.K2m` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The left part has two labelled hubs and the right part has m labelled leaves.

**Definition 1.2 (Decidable adjacency).**

$$\forall m \in \mathrm{Nat},\; \operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(\operatorname{K2m}\left(m\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.K2m_dec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Adjacency is decidable.

**Definition 1.3 (The sharp product constant).**

$$\forall m \in \mathrm{Nat},\; \operatorname{sharpConstant}\left(m\right) = (m + 2) \cdot (m + \frac{1}{m})$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.sharpConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constant is (m+2)(m+1/m), with every operation interpreted in the real numbers.

**Definition 1.4 (The nonzero splitting ratio).**

$$\forall m \in \mathrm{Nat},\; \operatorname{splitRatio}\left(m\right) = \operatorname{Real}.\operatorname{sqrt}\left(\frac{m - 2}{m + 2}\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.splitRatio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For m at least three, the splitting ratio is strictly between zero and one.

**Definition 1.5 (The attained maximum value).**

$$\forall m \in \mathrm{Nat},\; \forall R \in \mathrm{Real},\; \operatorname{maxValue}\left(m, R\right) = \frac{\operatorname{sharpConstant}\left(m\right)}{R}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.maxValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The resistance level is positive in the theorem; maxValue is the ratio C_m/R0.

**Definition 1.6 (The larger conductance).**

$$\forall m \in \mathrm{Nat},\; \forall R \in \mathrm{Real},\; \operatorname{plusConductance}\left(m, R\right) = (\frac{\operatorname{maxValue}\left(m, R\right)}{2}) \cdot (1 + \operatorname{splitRatio}\left(m\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.plusConductance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is t(1+rho)/2.

**Definition 1.7 (The smaller conductance).**

$$\forall m \in \mathrm{Nat},\; \forall R \in \mathrm{Real},\; \operatorname{minusConductance}\left(m, R\right) = (\frac{\operatorname{maxValue}\left(m, R\right)}{2}) \cdot (1 - \operatorname{splitRatio}\left(m\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.minusConductance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is t(1-rho)/2.

**Definition 1.8 (Equality of the labelled edge restriction).**

$$\forall m \in \mathrm{Nat},\; \forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right) \to \mathrm{Real},\; (\operatorname{EdgeRestriction}\left(m, a, b, w\right)) \Leftrightarrow (\forall i \in \operatorname{Fin}\left(m\right),\; (w\left(s(\operatorname{Fin}.\operatorname{castAdd}\left(m, 0\right),\operatorname{Fin}.\operatorname{natAdd}\left(2, i\right))\right) = a) \land (w\left(s(\operatorname{Fin}.\operatorname{castAdd}\left(m, 1\right),\operatorname{Fin}.\operatorname{natAdd}\left(2, i\right))\right) = b))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.EdgeRestriction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only the 2m labelled edges are compared. Values on all nonedges are unrestricted.

**Definition 1.9 (An explicit representative with constant leaf families).**

$$\forall m \in \mathrm{Nat},\; \forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall p \in \operatorname{Fin}\left(2 + m\right),\; \forall q \in \operatorname{Fin}\left(2 + m\right),\; \operatorname{uniformWeights}\left(m, a, b\right)\left(s(p,q)\right) = \operatorname{ite}\left((p = \operatorname{Fin}.\operatorname{castAdd}\left(m, 0\right)) \lor (q = \operatorname{Fin}.\operatorname{castAdd}\left(m, 0\right)), a, b\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.uniformWeights` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The representative assigns a to pairs containing the first hub and b otherwise. Its edge restriction is the required constant pair; its nonedge values are only a choice of representative.

**Definition 1.10 (Exchange of the two hubs).**

$$\forall m \in \mathrm{Nat},\; \forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right) \to \mathrm{Real},\; \forall e \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right),\; \operatorname{exchangeWeights}\left(m, w\right)\left(e\right) = w\left(\operatorname{Sym2}.\operatorname{map}\left(\operatorname{Equiv}.\operatorname{swap}\left(\operatorname{Fin}.\operatorname{castAdd}\left(m, 0\right), \operatorname{Fin}.\operatorname{castAdd}\left(m, 1\right)\right), e\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.exchangeWeights` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The swap fixes every leaf and interchanges the two labelled hubs.

**Definition 1.11 (The complete optimizer conclusion).**

$$\forall m \in \mathrm{Nat},\; \forall R \in \mathrm{Real},\; (\operatorname{OptimizerClaim}\left(m, R\right)) \Leftrightarrow ((\forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right) \to \mathrm{Real},\; (\forall e \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right),\; (e \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(\operatorname{K2m}\left(m\right)\right)) \Rightarrow (0 < w\left(e\right))) \Rightarrow ((\operatorname{totalRes}\left(\operatorname{K2m}\left(m\right), w\right) = R) \Rightarrow (\operatorname{lambda2}\left(\operatorname{K2m}\left(m\right), w\right) \le \operatorname{maxValue}\left(m, R\right)))) \land (((\forall e \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right),\; (e \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(\operatorname{K2m}\left(m\right)\right)) \Rightarrow (0 < \operatorname{uniformWeights}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right)\right)\left(e\right))) \land ((\operatorname{totalRes}\left(\operatorname{K2m}\left(m\right), \operatorname{uniformWeights}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right)\right)\right) = R) \land ((\operatorname{lambda2}\left(\operatorname{K2m}\left(m\right), \operatorname{uniformWeights}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right)\right)\right) = \operatorname{maxValue}\left(m, R\right)) \land (\operatorname{EdgeRestriction}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right), \operatorname{uniformWeights}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right)\right)\right))))) \land (((\forall e \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right),\; (e \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(\operatorname{K2m}\left(m\right)\right)) \Rightarrow (0 < \operatorname{uniformWeights}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right)\right)\left(e\right))) \land ((\operatorname{totalRes}\left(\operatorname{K2m}\left(m\right), \operatorname{uniformWeights}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right)\right)\right) = R) \land ((\operatorname{lambda2}\left(\operatorname{K2m}\left(m\right), \operatorname{uniformWeights}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right)\right)\right) = \operatorname{maxValue}\left(m, R\right)) \land (\operatorname{EdgeRestriction}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right), \operatorname{uniformWeights}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right)\right)\right))))) \land ((\forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right) \to \mathrm{Real},\; (\forall e \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right),\; (e \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(\operatorname{K2m}\left(m\right)\right)) \Rightarrow (0 < w\left(e\right))) \Rightarrow ((\operatorname{totalRes}\left(\operatorname{K2m}\left(m\right), w\right) = R) \Rightarrow ((\operatorname{lambda2}\left(\operatorname{K2m}\left(m\right), w\right) = \operatorname{maxValue}\left(m, R\right)) \Leftrightarrow ((\operatorname{EdgeRestriction}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right), w\right)) \lor (\operatorname{EdgeRestriction}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right), w\right)))))) \land ((\neg \left(\exists w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right) \to \mathrm{Real},\; (\operatorname{EdgeRestriction}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right), w\right)) \land (\operatorname{EdgeRestriction}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right), w\right))\right)) \land ((\forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right) \to \mathrm{Real},\; (\operatorname{EdgeRestriction}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right), w\right)) \Rightarrow (\operatorname{EdgeRestriction}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right), \operatorname{exchangeWeights}\left(m, w\right)\right))) \land ((\forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right) \to \mathrm{Real},\; (\operatorname{EdgeRestriction}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right), w\right)) \Rightarrow (\operatorname{EdgeRestriction}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right), \operatorname{exchangeWeights}\left(m, w\right)\right))) \land (\forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right) \to \mathrm{Real},\; \forall z \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right) \to \mathrm{Real},\; (\forall e \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right),\; (e \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(\operatorname{K2m}\left(m\right)\right)) \Rightarrow (w\left(e\right) = z\left(e\right))) \Rightarrow ((\operatorname{lambda2}\left(\operatorname{K2m}\left(m\right), w\right) = \operatorname{lambda2}\left(\operatorname{K2m}\left(m\right), z\right)) \land (\operatorname{totalRes}\left(\operatorname{K2m}\left(m\right), w\right) = \operatorname{totalRes}\left(\operatorname{K2m}\left(m\right), z\right)))))))))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.OptimizerClaim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The conjunction gives the upper bound, both explicit positive feasible attainments, the iff exclusion of every other labelled edge restriction, distinctness, exchange in both directions, and invariance under arbitrary nonedge changes.

**Definition 1.12 (The labelled hubs).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.hub`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.hub` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original hub coordinate is castAdd m j for j in Fin 2.

**Definition 1.13 (The labelled leaves).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.leaf`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.leaf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original leaf coordinate is natAdd 2 i for i in Fin m.

**Theorem 1.14 (No hub-to-hub edges).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.adj_hub_hub`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.adj_hub_hub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two hubs are never adjacent in K2m.

**Theorem 1.15 (No leaf-to-leaf edges).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.adj_leaf_leaf`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.adj_leaf_leaf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No two leaves are adjacent in K2m.

**Theorem 1.16 (Symmetry of the native weighted Laplacian).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_hermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite simple graph with decidable adjacency and every real pair-weight function, the original wLap is Hermitian.

**Theorem 1.17 (Native weighted edge action).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n,G,w,x and vertex i, the original matrix action is the sum over adjacent j of w(i,j)*(x i-x j).

**Theorem 1.18 (Constants lie in the native kernel).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n,G,w, the original Laplacian sends the all-ones vector to zero.

**Theorem 1.19 (The constant projector is Hermitian).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.proj_hermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.proj_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n, constProj n is Hermitian.

**Theorem 1.20 (The constant projector averages coordinates).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.proj_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.proj_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n,x,i, its matrix action at i is the coordinate sum of x divided by n.

**Theorem 1.21 (The constant quadratic form).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.proj_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.proj_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n,x, the constant-projector energy is the square of the coordinate sum divided by n.

**Theorem 1.22 (Idempotence of the constant projector).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.proj_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.proj_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive n, constProj n squared equals itself.

**Theorem 1.23 (The original Laplacian annihilates constants).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_proj`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_proj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n,G,w, wLap G w times constProj n is zero.

**Theorem 1.24 (The native Laplacian image has sum zero).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n,G,w,x, the coordinate sum of wLap G w acting on x is zero.

**Definition 1.25 (Original pair-difference vector).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.delta`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every n,p,q, delta p q is the difference of the two standard coordinate vectors.

**Theorem 1.26 (Pair differences have zero sum).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.delta_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.delta_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n,p,q, the coordinate sum of delta p q is zero.

**Theorem 1.27 (Pair differences read coordinate gaps).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.delta_dot`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.delta_dot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n,p,q,x, dotProduct (delta p q) x equals x p-x q.

**Theorem 1.28 (Distinct pair differences are nonzero).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.delta_ne`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.delta_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n and distinct p,q, delta p q is nonzero.

**Theorem 1.29 (The constant projector kills pair differences).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.proj_delta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.proj_delta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n,p,q, constProj n acting on delta p q is zero.

**Theorem 1.30 (Symmetric pair sums count unordered pairs twice).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.double_sum_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.double_sum_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n and symmetric real pair function f with zero diagonal, the sum over all ordered pairs equals twice the sum over i less than j.

**Theorem 1.31 (Independent-part pair-gap identity).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.pair_gap_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.pair_gap_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m, real function s on Fin m and real t, the ordered off-diagonal sum of s i+s j-2*t equals 2*(m-1)*(sum s-m*t).

**Definition 1.32 (The constant-space projection matrix).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.constProj`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.constProj` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every entry is the reciprocal of the number of vertices.

**Theorem 1.33 (The native zero eigenvalue has multiplicity one).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.zero_eigenvalue_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.zero_eigenvalue_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m positive and every positive edge weighting of K2m, exactly one indexed native Hermitian eigenvalue is zero.

**Theorem 1.34 (The Rayleigh value and the native eigenvalues).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lambda2_spectral`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lambda2_spectral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m positive and every positive edge weighting, lambda2 is positive, L-lambda2*(I-P) is positive semidefinite, and every nonzero native eigenvalue is at least lambda2.

**Theorem 1.35 (Harmonic all-pairs resistance and the native spectrum).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.resistance_spectral`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.resistance_spectral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m positive and every positive edge weighting, the harmonic totalRes is (m+2) times the sum of reciprocal native Hermitian eigenvalues, with the zero inverse interpreted as zero.

**Definition 1.36 (The two conductances incident to a leaf).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.leafSum`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.leafSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original leafSum is the sum of its two hub-to-leaf conductances.

**Theorem 1.37 (The native Laplacian trace).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace equals twice the sum of all leafSum values, for arbitrary real weights.

**Theorem 1.38 (The sharp product bound and its trace equality consequence).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.product_bound_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.product_bound_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least three and positive edge weighting, lambda2*totalRes is at most C_m; equality forces the sum of leafSum values to be m*lambda2.

**Theorem 1.39 (The positive uniform parameters forced by equality).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.equality_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.equality_parameters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Product equality forces positive a and b, common across every leaf, with a+b=lambda2 and (m+2)*a*b=lambda2 squared.

**Theorem 1.40 (The explicit representative has its prescribed edge restriction).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.uniformWeights_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.uniformWeights_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original uniformWeights representative has first-hub conductance a and second-hub conductance b on every leaf.

**Theorem 1.41 (Bounds and square of the splitting ratio).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.splitRatio_facts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.splitRatio_facts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least three, splitRatio is strictly between zero and one and its square is (m-2)/(m+2).

**Theorem 1.42 (Both common-sign quadratic solutions).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.parameter_roots`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.parameter_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least three, if a+b=t and (m+2)*a*b=t squared, then the ordered pair is t/2*(1+rho),t/2*(1-rho), or the reverse pair.

**Theorem 1.43 (The extremal Rayleigh and harmonic resistance values).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.uniform_extremal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.uniform_extremal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least three and positive a,b,t satisfying a+b=t and (m+2)*a*b=t squared, any positive K2m weighting with that edge restriction has lambda2=t and totalRes=C_m/t.

**Theorem 1.44 (Hub exchange interchanges the two edge families).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.exchange_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.exchange_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original hub swap maps EdgeRestriction a b to EdgeRestriction b a for arbitrary real a and b.

**Theorem 1.45 (The fixed-resistance maximum and all maximizers).**

$$\forall m \in \mathrm{Nat},\; (3 \le m) \Rightarrow (\forall R \in \mathrm{Real},\; (0 < R) \Rightarrow ((\forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right) \to \mathrm{Real},\; (\forall e \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right),\; (e \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(\operatorname{K2m}\left(m\right)\right)) \Rightarrow (0 < w\left(e\right))) \Rightarrow ((\operatorname{totalRes}\left(\operatorname{K2m}\left(m\right), w\right) = R) \Rightarrow (\operatorname{lambda2}\left(\operatorname{K2m}\left(m\right), w\right) \le \operatorname{maxValue}\left(m, R\right)))) \land (((\forall e \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right),\; (e \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(\operatorname{K2m}\left(m\right)\right)) \Rightarrow (0 < \operatorname{uniformWeights}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right)\right)\left(e\right))) \land ((\operatorname{totalRes}\left(\operatorname{K2m}\left(m\right), \operatorname{uniformWeights}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right)\right)\right) = R) \land ((\operatorname{lambda2}\left(\operatorname{K2m}\left(m\right), \operatorname{uniformWeights}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right)\right)\right) = \operatorname{maxValue}\left(m, R\right)) \land (\operatorname{EdgeRestriction}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right), \operatorname{uniformWeights}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right)\right)\right))))) \land (((\forall e \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right),\; (e \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(\operatorname{K2m}\left(m\right)\right)) \Rightarrow (0 < \operatorname{uniformWeights}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right)\right)\left(e\right))) \land ((\operatorname{totalRes}\left(\operatorname{K2m}\left(m\right), \operatorname{uniformWeights}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right)\right)\right) = R) \land ((\operatorname{lambda2}\left(\operatorname{K2m}\left(m\right), \operatorname{uniformWeights}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right)\right)\right) = \operatorname{maxValue}\left(m, R\right)) \land (\operatorname{EdgeRestriction}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right), \operatorname{uniformWeights}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right)\right)\right))))) \land ((\forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right) \to \mathrm{Real},\; (\forall e \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right),\; (e \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(\operatorname{K2m}\left(m\right)\right)) \Rightarrow (0 < w\left(e\right))) \Rightarrow ((\operatorname{totalRes}\left(\operatorname{K2m}\left(m\right), w\right) = R) \Rightarrow ((\operatorname{lambda2}\left(\operatorname{K2m}\left(m\right), w\right) = \operatorname{maxValue}\left(m, R\right)) \Leftrightarrow ((\operatorname{EdgeRestriction}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right), w\right)) \lor (\operatorname{EdgeRestriction}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right), w\right)))))) \land ((\neg \left(\exists w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right) \to \mathrm{Real},\; (\operatorname{EdgeRestriction}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right), w\right)) \land (\operatorname{EdgeRestriction}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right), w\right))\right)) \land ((\forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right) \to \mathrm{Real},\; (\operatorname{EdgeRestriction}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right), w\right)) \Rightarrow (\operatorname{EdgeRestriction}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right), \operatorname{exchangeWeights}\left(m, w\right)\right))) \land ((\forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right) \to \mathrm{Real},\; (\operatorname{EdgeRestriction}\left(m, \operatorname{minusConductance}\left(m, R\right), \operatorname{plusConductance}\left(m, R\right), w\right)) \Rightarrow (\operatorname{EdgeRestriction}\left(m, \operatorname{plusConductance}\left(m, R\right), \operatorname{minusConductance}\left(m, R\right), \operatorname{exchangeWeights}\left(m, w\right)\right))) \land (\forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right) \to \mathrm{Real},\; \forall z \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right) \to \mathrm{Real},\; (\forall e \in \operatorname{Sym2}\left(\operatorname{Fin}\left(2 + m\right)\right),\; (e \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(\operatorname{K2m}\left(m\right)\right)) \Rightarrow (w\left(e\right) = z\left(e\right))) \Rightarrow ((\operatorname{lambda2}\left(\operatorname{K2m}\left(m\right), w\right) = \operatorname{lambda2}\left(\operatorname{K2m}\left(m\right), z\right)) \land (\operatorname{totalRes}\left(\operatorname{K2m}\left(m\right), w\right) = \operatorname{totalRes}\left(\operatorname{K2m}\left(m\right), z\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weighted energy is a sum of positive edge squares, so its kernel is exactly the constants. The inverse of L+P, for the constant projection P, constructs the unique harmonic voltage for every distinct boundary pair. Summing its reciprocal-current expression gives R=(m+2) trace(L+) and then the reciprocal-eigenvalue formula. Leaf-difference Rayleigh tests give trace L at least 2m lambda2. The reciprocal eigenvalue estimate gives lambda2 R at most C_m. Equality forces trace equality and makes every leaf difference a lambda2 eigenvector, hence both conductance families are constant across leaves. Exact unit-current solutions give the uniform-case resistance formula and force a+b=t and (m+2)ab=t squared. These equations have exactly the two common-sign solutions. A positive quadratic-form certificate proves lambda2=t on either solution; the resistance formula gives R=R0. Thus the maximum is attained without compactness or zero-conductance relaxation. The proof reuses the original Rayleigh certificate, reciprocal-trace theorem and nonedge invariance.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.EdgeRestriction`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.K2m`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.K2m_dec`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.OptimizerClaim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.adj_hub_hub`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.adj_leaf_leaf`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.constProj`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.delta`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.delta_dot`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.delta_ne`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.delta_sum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.double_sum_lt`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.equality_parameters`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.exchangeWeights`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.exchange_edges`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.hub`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lambda2_spectral`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_hermitian`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_mul`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_one`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_proj`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_sum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.lap_trace`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.leaf`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.leafSum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.maxValue`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.minusConductance`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.pair_gap_sum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.parameter_roots`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.plusConductance`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.product_bound_trace`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.proj_delta`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.proj_energy`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.proj_hermitian`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.proj_mul`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.proj_sq`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.resistance_spectral`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.result`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.sharpConstant`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.splitRatio`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.splitRatio_facts`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.uniformWeights`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.uniformWeights_edges`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.uniform_extremal`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.zero_eigenvalue_count`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation](AlbrightKemenyEdgeDerivativeRefutation.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation](FiedlerResistanceInvariantWeightsRefutation.md)
