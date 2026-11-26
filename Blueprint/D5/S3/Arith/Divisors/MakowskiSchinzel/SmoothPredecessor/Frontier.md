# Frontier refinement of the smooth fold

## Abstract

Frontier refinement of the smooth fold

**Theorem 1.1 (Refinement preserves the smooth fold).**

$$\forall w \in \mathbb{N} \to \mathbb{N},\; \forall X \in \mathbb{N},\; \forall leaf \in \operatorname{Pair}\left(\operatorname{List}\left(\mathbb{N}\right), \mathbb{N}\right) \to Bool,\; \forall k \in \mathbb{N},\; \forall ps \in \operatorname{List}\left(\mathbb{N}\right),\; \forall c \in \mathbb{N},\; \operatorname{sum}\left(\operatorname{mapSmoothSum}\left(w, X, \operatorname{refine}\left(X, leaf, k, \operatorname{pair}\left(ps, c\right)\right)\right)\right) = \operatorname{smoothSum}\left(w, ps, X, c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Frontier.sum_refine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

For a node (p::ps,c), powList visits c p^e starting at exponent zero, stopping at the first value above X or after 64 steps. The visited starts give the child nodes (ps,c p^e), refined depth first. A node with no generators is retained. Refinement also keeps a node that passes the stopping test leaf or lies k levels below the root. Each expansion splits smoothSum along the powers of the first generator, so for every weight w, stopping test and depth the node sum of the refinement equals the fold of the root.

**Theorem 1.2 (A checked frontier carries the root fold).**

$$\forall w \in \mathbb{N} \to \mathbb{N},\; \forall X \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall ps \in \operatorname{List}\left(\mathbb{N}\right),\; \forall c \in \mathbb{N},\; \forall F \in \operatorname{List}\left(\operatorname{Pair}\left(\operatorname{List}\left(\mathbb{N}\right), \mathbb{N}\right)\right),\; \operatorname{frontierOk}\left(X, k, \operatorname{pair}\left(ps, c\right), F\right) = true \Rightarrow \operatorname{smoothSum}\left(w, ps, X, c\right) = \operatorname{sum}\left(\operatorname{mapSmoothSum}\left(w, X, F\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Frontier.smoothSum_eq_of_frontierOk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

The test frontierOk X k (ps,c) F is true when the refinement of (ps,c) to depth k, stopped at the nodes of F, returns exactly the list F. By the refinement identity, for every weight w the root fold then equals the mapped sum of smoothSum w ps X c over (ps,c) in F. List.map_append and List.sum_append split concatenated frontiers directly.

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Frontier.smoothSum_eq_of_frontierOk`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Frontier.sum_refine`
