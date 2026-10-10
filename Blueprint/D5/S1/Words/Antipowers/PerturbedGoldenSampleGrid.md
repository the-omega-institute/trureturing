# Perturbed Golden Sample Grids

## Abstract

A signed rational approximation separates a parity sample grid by golden cylinder cuts.

**Definition 1.1 (Rank in a finite cut set).**

$$\forall T \in \operatorname{Finset}\left(\mathbb{R}\right),\; \forall x \in \mathbb{R},\; \operatorname{rank}\left(T, x\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(\operatorname{fun} (c : \mathbb{R}) \mapsto c \le x, T\right)\right)$$

*Formalization.* `D5/S1/Words/Antipowers/PerturbedGoldenSampleGrid.rank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rank counts cuts at or below x. The filter is over real numbers, with the half-open convention that a cut belongs to the cell on its right.

**Definition 1.2 (Signed sampling error).**

$$\forall s \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall j \in \mathbb{N},\; \operatorname{error}\left(s, d, j\right) = -s \cdot d - \frac{\operatorname{Nat}.\operatorname{cast}\left(j\right) \cdot d^{2}}{2}$$

*Formalization.* `D5/S1/Words/Antipowers/PerturbedGoldenSampleGrid.error` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first error term is signed and the quadratic drift is nonpositive. Nat.cast in these formulas takes its value in the real numbers.

**Definition 1.3 (Parity sample lift).**

$$\forall q \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall s \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall j \in \mathbb{N},\; \operatorname{Y}\left(q, p, s, d, j\right) = \operatorname{Nat}.\operatorname{cast}\left(p\right) + (\operatorname{if} \operatorname{Nat}.\operatorname{mod}\left(j, 2\right) = 0 \operatorname{then} 0 \operatorname{else} \frac{\operatorname{Nat}.\operatorname{cast}\left(q\right)}{2}) + s \cdot \operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{div}\left(j, 2\right)\right) + (\operatorname{if} \operatorname{Nat}.\operatorname{mod}\left(j, 2\right) = 0 \operatorname{then} 0 \operatorname{else} \frac{s}{2}) + \operatorname{error}\left(s, d, j\right)$$

*Formalization.* `D5/S1/Words/Antipowers/PerturbedGoldenSampleGrid.Y` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nat.div and Nat.mod denote natural floor division and remainder. Even indices start in the integer parity class; odd indices start half a period away.

**Lemma 1.4 (Sampling lift identity).**

$$\forall q \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall s \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall j \in \mathbb{N},\; \operatorname{Nat}.\operatorname{cast}\left(p\right) + \frac{\operatorname{Nat}.\operatorname{cast}\left(j\right) \cdot \operatorname{Nat}.\operatorname{cast}\left(q\right)}{2} + \frac{s \cdot \operatorname{Nat}.\operatorname{cast}\left(j\right)}{2} + \operatorname{error}\left(s, d, j\right) = \operatorname{Y}\left(q, p, s, d, j\right) + \operatorname{Nat}.\operatorname{cast}\left(q\right) \cdot \operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{div}\left(j, 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Antipowers/PerturbedGoldenSampleGrid.sampling_lift_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Splitting j into twice its natural quotient by 2 plus its remainder produces the parity lift. The discarded part is a whole multiple of q.

**Theorem 1.5 (Distinct samples occupy distinct golden cylinders).**

$$\forall q \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall s \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall i \in \mathbb{N},\; \forall j \in \mathbb{N},\; ((0 < q) \land \left((\operatorname{Even}\left(q\right)) \land \left((\operatorname{Nat}.\operatorname{Coprime}\left(p, q\right)) \land \left(((s = 1) \lor (s = -1)) \land \left((0 < d) \land \left((\operatorname{Nat}.\operatorname{cast}\left(q\right) \cdot d < \frac{9}{20}) \land \left((d + \frac{\operatorname{Nat}.\operatorname{cast}\left(q\right) \cdot d^{2}}{2} < \frac{49}{2000}) \land \left((\operatorname{Nat}.\operatorname{cast}\left(q\right) \cdot \operatorname{goldenMechanicalSlope}\left(\right) = \operatorname{Nat}.\operatorname{cast}\left(p\right) - s \cdot d) \land \left((i < q - 1) \land \left((j < q - 1) \land (i \ne j)\right)\right)\right)\right)\right)\right)\right)\right)\right)) \Rightarrow (\operatorname{rank}\left(\operatorname{goldenCylinderEndpointSet}\left(q - 1\right), \operatorname{Int}.\operatorname{fract}\left(\frac{\operatorname{Y}\left(q, p, s, d, i\right)}{\operatorname{Nat}.\operatorname{cast}\left(q\right)}\right)\right) \ne \operatorname{rank}\left(\operatorname{goldenCylinderEndpointSet}\left(q - 1\right), \operatorname{Int}.\operatorname{fract}\left(\frac{\operatorname{Y}\left(q, p, s, d, j\right)}{\operatorname{Nat}.\operatorname{cast}\left(q\right)}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Antipowers/PerturbedGoldenSampleGrid.golden_sample_grid_rank_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary coprime numerator p and positive even denominator q, a signed golden-slope residual satisfying the two strict bounds separates every pair of indices below q−1. The proof constructs ordered periodic cuts from the inverse of p modulo q, puts each parity sample strictly between its cuts, and proves that its cell label is distinct modulo q. No Fibonacci-index assumption is needed.

## References

- Truth anchor: `D5/S1/Words/Antipowers/PerturbedGoldenSampleGrid.Y`
- Truth anchor: `D5/S1/Words/Antipowers/PerturbedGoldenSampleGrid.error`
- Truth anchor: `D5/S1/Words/Antipowers/PerturbedGoldenSampleGrid.golden_sample_grid_rank_injective`
- Truth anchor: `D5/S1/Words/Antipowers/PerturbedGoldenSampleGrid.rank`
- Truth anchor: `D5/S1/Words/Antipowers/PerturbedGoldenSampleGrid.sampling_lift_identity`
