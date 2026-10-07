# Boundary cone decomposition

## Abstract

Two boundary mass inequalities yield a finite conical decomposition into thirty-three explicitly listed rays.

**Definition 1.1 (Bottom-six mass row).**

$$firstRow=[-1,-2,-3,-2,-1,0,1,2,3]$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/BoundaryConeDecomposition.firstRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is a function Fin 9 → ℝ, displayed in increasing Fin index order.

**Definition 1.2 (Bottom-three mass row).**

$$secondRow=[-1,-1,-1,-1,-1,-1,0,1,2]$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/BoundaryConeDecomposition.secondRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is a function Fin 9 → ℝ, displayed in increasing Fin index order.

**Definition 1.3 (Thirty-three boundary rays).**

$$rays=[[0,0,0,0,0,0,1,0,0],[0,0,0,0,0,0,0,1,0],[0,0,0,0,0,0,0,0,1],[1,0,0,0,0,0,0,1,0],[2,0,0,0,0,0,0,0,1],[0,2,0,0,0,0,0,2,0],[0,1,0,0,0,0,0,1,0],[0,3,0,0,0,0,0,0,2],[0,0,2,0,0,0,0,3,0],[0,0,3,0,0,0,0,0,3],[0,0,0,2,0,0,0,2,0],[0,0,0,1,0,0,0,1,0],[0,0,0,3,0,0,0,0,2],[0,0,0,0,1,0,0,1,0],[0,0,0,0,2,0,0,0,1],[0,0,0,0,0,1,0,1,0],[0,0,0,0,0,2,0,0,1],[1,1,0,0,0,0,0,0,1],[1,0,1,0,0,0,0,2,0],[3,0,1,0,0,0,0,0,2],[1,0,0,1,0,0,0,0,1],[0,1,0,0,1,0,0,0,1],[0,3,0,0,0,1,0,0,2],[0,2,0,0,0,0,1,0,1],[0,0,1,0,1,0,0,2,0],[0,0,1,0,3,0,0,0,2],[0,0,2,0,0,1,0,3,0],[0,0,3,0,0,3,0,0,3],[0,0,1,0,0,0,1,1,0],[0,0,2,0,0,0,3,0,1],[0,0,0,1,1,0,0,0,1],[0,0,0,3,0,1,0,0,2],[0,0,0,2,0,0,1,0,1]]$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/BoundaryConeDecomposition.rays` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed table has type Fin 33 → (Fin 9 → ℝ). Every row has nine real entries; the outer index order is 0 through 32.

**Theorem 1.4 (Transfer from the ray table).**

$$\forall (Good:(Fin\left(9\right)\to \mathbb{R})\to Prop), ((Good\left(0\right))\land (\forall (u:Fin\left(9\right)\to \mathbb{R}), \forall (w:Fin\left(9\right)\to \mathbb{R}), ((Good\left(u\right))\land (Good\left(w\right)))\Rightarrow Good\left(u+w\right))\land (\forall (t:\mathbb{R}), \forall (u:Fin\left(9\right)\to \mathbb{R}), ((0\leq t)\land (Good\left(u\right)))\Rightarrow Good\left(t\cdot u\right))\land (\forall (r:Fin\left(33\right)), Good\left(rays\left(r\right)\right)))\Rightarrow \forall (y:Fin\left(9\right)\to \mathbb{R}), ((\forall (j:Fin\left(9\right)), 0\leq y\left(j\right))\land (0\leq \sum_{j:Fin\left(9\right)} y\left(j\right)\cdot firstRow\left(j\right))\land (0\leq \sum_{j:Fin\left(9\right)} y\left(j\right)\cdot secondRow\left(j\right)))\Rightarrow Good\left(y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/BoundaryConeDecomposition.finite_cone_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A predicate containing zero and closed under addition and nonnegative scalar multiplication contains every nonnegative vector satisfying the two row inequalities whenever it contains all thirty-three rays. Two successive positive-negative mass decompositions express each admissible vector as a nonnegative combination of the listed rays.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/BoundaryConeDecomposition.finite_cone_transfer`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/BoundaryConeDecomposition.firstRow`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/BoundaryConeDecomposition.rays`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/BoundaryConeDecomposition.secondRow`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer](HalfspaceConeTransfer.md)
