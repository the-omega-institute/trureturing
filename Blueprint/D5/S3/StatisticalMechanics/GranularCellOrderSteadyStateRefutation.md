# Granular cell-order steady states need not be unique

## Abstract

Strictly positive merging and splitting rates admit two distinct positive normalized stationary cell-order distributions at C = 10.

Cell orders are natural numbers from 3 through C. The real-valued function Q gives their fractions, and p and q give the constant merging and splitting rates. Rates are evaluated at the smaller and larger input orders, respectively. All index subtraction is natural-number subtraction, truncated at zero. Only values of Q on the interval from 3 through C enter physicality and the equality conclusion.

**Definition 1.1 (The merging and splitting channels).**

$$\forall (C: \mathbb{N}), (\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.J}\left(C\right) = \operatorname{Finset.filter}\left(\lambda (a: (\mathbb{N} \times \mathbb{N})) \mapsto ((a.1 \le a.2) \land (((a.1) + (a.2)) - (2) \le C)), \operatorname{Finset.product}\left(\operatorname{Finset.Icc}\left(3, C\right), \operatorname{Finset.Icc}\left(3, C\right)\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.J` (`✓ std3`).

*Citation.* Alex D. C. Myhill, Raphael Blumenfeld (2023). *Steady states of two-dimensional granular systems are unique, stable, and sometimes satisfy detailed balance*. DOI: [10.1088/1751-8121/ace56d](https://doi.org/10.1088/1751-8121/ace56d). URL: <https://arxiv.org/abs/2306.10526v2>.

*Commentary.*

A channel consists of two input orders i and j with 3 <= i <= j <= C and product order i + j - 2 <= C. Finset.product forms the Cartesian product of the two intervals; Finset.filter selects these channels.

**Definition 1.2 (The Kronecker delta).**

$$\forall (i: \mathbb{N}), (\forall (j: \mathbb{N}), ((\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.delta}\left(i, j\right): \mathbb{R}) = \mathrm{if} (i = j) \mathrm{then} 1 \mathrm{else} 0))$$

*Formalization.* `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.delta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alex D. C. Myhill, Raphael Blumenfeld (2023). *Steady states of two-dimensional granular systems are unique, stable, and sometimes satisfy detailed balance*. DOI: [10.1088/1751-8121/ace56d](https://doi.org/10.1088/1751-8121/ace56d). URL: <https://arxiv.org/abs/2306.10526v2>.

*Commentary.*

The counting factors in equations (1) and (2) use the Kronecker delta, equal to one for equal orders and zero otherwise.

**Definition 1.3 (The net channel flux).**

$$\forall (p: (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right))), (\forall (q: (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right))), (\forall (Q: (\mathbb{N} \to \mathbb{R})), (\forall (i: \mathbb{N}), (\forall (j: \mathbb{N}), ((\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.flux}\left(p, q, Q, i, j\right): \mathbb{R}) = (((p\left(\operatorname{min}\left(i, j\right), \operatorname{max}\left(i, j\right)\right)) \cdot (Q\left(i\right))) \cdot (Q\left(j\right))) - ((q\left(\operatorname{min}\left(i, j\right), \operatorname{max}\left(i, j\right)\right)) \cdot (Q\left(((i) + (j)) - (2)\right))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.flux` (`✓ std3`).

*Citation.* Alex D. C. Myhill, Raphael Blumenfeld (2023). *Steady states of two-dimensional granular systems are unique, stable, and sometimes satisfy detailed balance*. DOI: [10.1088/1751-8121/ace56d](https://doi.org/10.1088/1751-8121/ace56d). URL: <https://arxiv.org/abs/2306.10526v2>.

*Commentary.*

Section I.A defines the net flux as the merging rate times the two input fractions, minus the splitting rate times the product-cell fraction. The min and max arguments let both orders of the input pair use the same channel rates.

**Definition 1.4 (The evolution of a cell-order fraction).**

$$\forall (C: \mathbb{N}), (\forall (p: (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right))), (\forall (q: (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right))), (\forall (Q: (\mathbb{N} \to \mathbb{R})), (\forall (k: \mathbb{N}), ((\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.rhs}\left(C, p, q, Q, k\right): \mathbb{R}) = ((((\frac{1}{2}: \mathbb{R})) \cdot (\sum_{(i: \mathbb{N}) \in \operatorname{Finset.Icc}\left(3, (k) - (1)\right)} ((\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.flux}\left(p, q, Q, i, ((k) - (i)) + (2)\right)) \cdot ((1) + (\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.delta}\left(i, ((k) - (i)) + (2)\right)))))) - (\sum_{(i: \mathbb{N}) \in \operatorname{Finset.Icc}\left((k) + (1), C\right)} ((\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.flux}\left(p, q, Q, k, ((i) - (k)) + (2)\right)) \cdot ((1) + (\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.delta}\left(i, ((2) \cdot (k)) - (2)\right)))))) + ((Q\left(k\right)) \cdot (\sum_{(a: (\mathbb{N} \times \mathbb{N})) \in \operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.J}\left(C\right)} (\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.flux}\left(p, q, Q, a.1, a.2\right)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.rhs` (`✓ std3`).

*Citation.* Alex D. C. Myhill, Raphael Blumenfeld (2023). *Steady states of two-dimensional granular systems are unique, stable, and sometimes satisfy detailed balance*. DOI: [10.1088/1751-8121/ace56d](https://doi.org/10.1088/1751-8121/ace56d). URL: <https://arxiv.org/abs/2306.10526v2>.

*Commentary.*

This is equation (1) read with the net flux of Section I.A. The first sum creates k-cells, the second removes them, and the last term accounts for the changing total number of cells. The factor one half and the delta factors count equal input orders correctly. The printed loss term's splitting factor is read as the product-cell fraction Q_i, as in equation (2).

**Definition 1.5 (Strictly positive channel rates).**

$$\forall (C: \mathbb{N}), (\forall (p: (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right))), (\forall (q: (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right))), ((\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.PositiveRates}\left(C, p, q\right)) \Leftrightarrow (\forall (a: (\mathbb{N} \times \mathbb{N})), ((a \in \operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.J}\left(C\right)) \Rightarrow ((0 < p\left(a.1, a.2\right)) \land (0 < q\left(a.1, a.2\right))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.PositiveRates` (`✓ std3`).

*Citation.* Alex D. C. Myhill, Raphael Blumenfeld (2023). *Steady states of two-dimensional granular systems are unique, stable, and sometimes satisfy detailed balance*. DOI: [10.1088/1751-8121/ace56d](https://doi.org/10.1088/1751-8121/ace56d). URL: <https://arxiv.org/abs/2306.10526v2>.

*Commentary.*

Both the merging rate and the splitting rate are strictly positive on every channel in J C. Values of the rate functions outside these channels are unrestricted.

**Definition 1.6 (Positive normalized cell fractions).**

$$\forall (C: \mathbb{N}), (\forall (Q: (\mathbb{N} \to \mathbb{R})), ((\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.Physical}\left(C, Q\right)) \Leftrightarrow ((\forall (k: \mathbb{N}), ((3 \le k) \Rightarrow ((k \le C) \Rightarrow (0 < Q\left(k\right))))) \land (\sum_{(k: \mathbb{N}) \in \operatorname{Finset.Icc}\left(3, C\right)} (Q\left(k\right)) = 1))))$$

*Formalization.* `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.Physical` (`✓ std3`).

*Citation.* Alex D. C. Myhill, Raphael Blumenfeld (2023). *Steady states of two-dimensional granular systems are unique, stable, and sometimes satisfy detailed balance*. DOI: [10.1088/1751-8121/ace56d](https://doi.org/10.1088/1751-8121/ace56d). URL: <https://arxiv.org/abs/2306.10526v2>.

*Commentary.*

A physical state has a strictly positive real fraction at each order from 3 through C, and these fractions sum to one. Values outside that interval are unrestricted.

**Definition 1.7 (Vanishing evolution at every cell order).**

$$\forall (C: \mathbb{N}), (\forall (p: (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right))), (\forall (q: (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right))), (\forall (Q: (\mathbb{N} \to \mathbb{R})), ((\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.Stationary}\left(C, p, q, Q\right)) \Leftrightarrow (\forall (k: \mathbb{N}), ((3 \le k) \Rightarrow ((k \le C) \Rightarrow (\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.rhs}\left(C, p, q, Q, k\right) = 0))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.Stationary` (`✓ std3`).

*Citation.* Alex D. C. Myhill, Raphael Blumenfeld (2023). *Steady states of two-dimensional granular systems are unique, stable, and sometimes satisfy detailed balance*. DOI: [10.1088/1751-8121/ace56d](https://doi.org/10.1088/1751-8121/ace56d). URL: <https://arxiv.org/abs/2306.10526v2>.

*Commentary.*

A stationary state makes the full right-hand side vanish at every order from 3 through C. No separate condition on individual fluxes or their total is imposed.

**Definition 1.8 (The universal steady-state uniqueness conjecture).**

$$(\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.claim}) \Leftrightarrow (\forall (C: \mathbb{N}), ((3 \le C) \Rightarrow (\forall (p: (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right))), (\forall (q: (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right))), ((\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.PositiveRates}\left(C, p, q\right)) \Rightarrow (\forall (Q: (\mathbb{N} \to \mathbb{R})), (\forall (Q': (\mathbb{N} \to \mathbb{R})), ((\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.Physical}\left(C, Q\right)) \Rightarrow ((\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.Physical}\left(C, Q'\right)) \Rightarrow ((\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.Stationary}\left(C, p, q, Q\right)) \Rightarrow ((\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.Stationary}\left(C, p, q, Q'\right)) \Rightarrow (\forall (k: \mathbb{N}), ((3 \le k) \Rightarrow ((k \le C) \Rightarrow (Q\left(k\right) = Q'\left(k\right))))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.claim` (`✓ std3`).

*Citation.* Alex D. C. Myhill, Raphael Blumenfeld (2023). *Steady states of two-dimensional granular systems are unique, stable, and sometimes satisfy detailed balance*. DOI: [10.1088/1751-8121/ace56d](https://doi.org/10.1088/1751-8121/ace56d). URL: <https://arxiv.org/abs/2306.10526v2>.

*Commentary.*

Sections I.D and III conjecture a unique physical steady state for any constant rates and any upper cell order. Here the uniqueness assertion quantifies over every natural C >= 3 and every pair of rate functions positive on J C: any two physical stationary states agree at every order from 3 through C. It does not assert equality outside that interval or the existence of a stationary state.

**Theorem 1.9 (Two stationary states at upper order ten).**

$$\neg (\operatorname{D5.S3.StatisticalMechanics.GranularCellOrderSteadyStateRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/myhill-blumenfeld-2023-granular-steady-state-uniqueness-refutation` (refuted) by `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"myhill-blumenfeld-2023-granular-steady-state-uniqueness-refutation","declaration_gid":"D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Alex D. C. Myhill, Raphael Blumenfeld (2023). *Steady states of two-dimensional granular systems are unique, stable, and sometimes satisfy detailed balance*. DOI: [10.1088/1751-8121/ace56d](https://doi.org/10.1088/1751-8121/ace56d). URL: <https://arxiv.org/abs/2306.10526v2>.

*Commentary.*

Take C = 10. Its sixteen channels, in order, are (3,3), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), (4,4), (4,5), (4,6), (4,7), (4,8), (5,5), (5,6), (5,7), (6,6). Choose the merging rates p = (10/3, 2/3, 4/15, 4/3, 2/3, 2, 509018/225, 1, 35579/175, 2, 422/5, 2, 386/225, 30416/25, 255689/25, 4) and the splitting rates q = (1, 2/5, 2, 972/5, 2, 2, 2138/75, 141/10, 1, 2, 2, 3967/35, 35878/315, 2, 233557/35, 2). All these rates are strictly positive.

In order from 3 through 10, take X = (3, 2, 5, 1, 2, 1, 1, 1)/16 and Y = (12, 6, 5, 4, 4, 1, 1, 1)/34, with zero values at other orders. Both states have strictly positive fractions on this interval and sum to one. At each state all eight balance rows of equation (2) vanish, and the total flux over J 10 is zero. Thus the full right-hand side vanishes at both states. Their order-three fractions differ: X_3 = 3/16 and Y_3 = 6/17. These two physical stationary states refute the uniqueness assertion.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.J`
- Truth anchor: `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.Physical`
- Truth anchor: `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.PositiveRates`
- Truth anchor: `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.Stationary`
- Truth anchor: `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.delta`
- Truth anchor: `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.flux`
- Truth anchor: `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.result`
- Truth anchor: `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.rhs`
