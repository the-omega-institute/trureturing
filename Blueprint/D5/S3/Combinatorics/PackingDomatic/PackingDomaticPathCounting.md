# A Counting Bound for Packing Domatic Colourings

## Abstract

Endpoint occupancy and interior broadcast counts give a uniform lower bound on the palette.

**Theorem 1.1 (The palette lower bound).**

$$\forall n \in Nat,\; \forall k \in Nat,\; \forall t \in Nat,\; \forall f \in Fin\left(n\right) \to Nat,\; IsPackingDomatic\left(n, k, t, f\right) \Rightarrow \left(t + 1 \le n \Rightarrow 16 \cdot k \le 15 \cdot t + 12\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PackingDomatic/PackingDomaticPathCounting.local_counting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Boštjan Brešar, Jasmina Ferme, Wenjie Hu (2026). *Partitioning an S-packing coloring into broadcast dominating sets*. DOI: [10.48550/arXiv.2610.03477](https://doi.org/10.48550/arXiv.2610.03477). URL: <https://arxiv.org/abs/2610.03477v1>.

*Commentary.*

Suppose P_n has a packing k-domatic colouring with colours at most t and n at least t+1. Let E be the vertices whose broadcasts reach vertex 0. Each partition class contributes a vertex to E, and the colours on E are distinct, so k is at most |E| and |E| is at most t. Put delta=t-|E| and d=t-k. If t is at least 16d+13, consider vertex z=8d+7 and put h=4d+3. At most t-h vertices of E reach z; at most delta+1 vertices outside E lie in the prefix 0 through t; and at most 2delta+1 vertices beyond that prefix reach z. The last bound follows by matching their distinct colours to missing endpoint colours or to endpoint vertices before z. These three bounds give fewer than k broadcasters at z, contradicting domination by all k classes. Consequently 16k is at most 15t+12.

## References

- Truth anchor: `D5/S3/Combinatorics/PackingDomatic/PackingDomaticPathCounting.local_counting`
- Dependency: [D5/S3/Combinatorics/PackingDomatic/PackingDomaticPathDefs](PackingDomaticPathDefs.md)
