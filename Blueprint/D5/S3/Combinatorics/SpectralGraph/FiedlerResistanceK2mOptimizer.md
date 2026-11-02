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

**Theorem 1.12 (The fixed-resistance maximum and all maximizers).**

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
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.exchangeWeights`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.maxValue`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.minusConductance`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.plusConductance`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.result`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.sharpConstant`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.splitRatio`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.uniformWeights`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation](AlbrightKemenyEdgeDerivativeRefutation.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation](FiedlerResistanceInvariantWeightsRefutation.md)
