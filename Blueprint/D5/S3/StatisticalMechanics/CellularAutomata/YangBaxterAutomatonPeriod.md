# The Yang-Baxter cellular automata over F_{2^n} have period dividing 2^n

## Abstract

For every finite field F of characteristic 2 and every bijection f of F satisfying f(x) + f(x + f(y)) = f(x + f(y + f(x))), the cellular automaton that runs the R-matrix R(x, y) = (y + f(x + y), x - f(x + y)) along a row of N cells with the helical boundary condition returns to its initial state after |F| steps, for every N. This proves the conjecture of A. Araoka and T. Tokihiro (arXiv:2602.17148), who proved it for |F| = 4 and 8.

**Definition 1.1 (The R-matrix).**

$$\operatorname{rmat}\left(f, x, y\right) = (y + f\left(x + y\right), x - f\left(x + y\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod.rmat` (`✓ std3`).

*Citation.* Aoi Araoka; Tetsuji Tokihiro (2026). *Integrable Cellular Automata on Finite Fields of Order 2^n*. DOI: [10.1007/s11040-026-09569-9](https://doi.org/10.1007/s11040-026-09569-9). URL: <https://arxiv.org/abs/2602.17148v1>.

*Commentary.*

The R-matrix of the paper, R(x, y) = (y + f(x + y), x - f(x + y)); its first output is the new cell value and its second output is passed to the next cell.

**Definition 1.2 (The auxiliary values).**

$$\operatorname{carry}\left(f, x, b, 0\right) = b,\qquad\operatorname{carry}\left(f, x, b, i + 1\right) = \operatorname{snd}\left(\operatorname{rmat}\left(f, x_{i}, \operatorname{carry}\left(f, x, b, i\right)\right)\right) (i < N)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod.carry` (`✓ std3`).

*Citation.* Aoi Araoka; Tetsuji Tokihiro (2026). *Integrable Cellular Automata on Finite Fields of Order 2^n*. DOI: [10.1007/s11040-026-09569-9](https://doi.org/10.1007/s11040-026-09569-9). URL: <https://arxiv.org/abs/2602.17148v1>.

*Commentary.*

The values passed along the row: y_0 = b is the boundary value, and y_(i+1) is the second output of R at cell i, for i < N.

**Definition 1.3 (One time step).**

$$\operatorname{step}\left(f, (x, b)\right) = ((\operatorname{fst}\left(\operatorname{rmat}\left(f, x_{i}, \operatorname{carry}\left(f, x, b, i\right)\right)\right))_{i < N}, \operatorname{carry}\left(f, x, b, N\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod.step` (`✓ std3`).

*Citation.* Aoi Araoka; Tetsuji Tokihiro (2026). *Integrable Cellular Automata on Finite Fields of Order 2^n*. DOI: [10.1007/s11040-026-09569-9](https://doi.org/10.1007/s11040-026-09569-9). URL: <https://arxiv.org/abs/2602.17148v1>.

*Commentary.*

One time step maps the cell values x_0, ..., x_(N-1) and the boundary value b to the first outputs of R at each cell and, by the helical boundary condition, the new boundary value y_N.

**Definition 1.4 (The conjecture).**

$$claim \Leftrightarrow (\forall F \in \operatorname{FiniteField},\; (\operatorname{char}\left(F\right) = 2) \Rightarrow \left((\operatorname{Bijective}\left(f\right)) \Rightarrow \left((\forall x \in F,\; \forall y \in F,\; f\left(x\right) + f\left(x + f\left(y\right)\right) = f\left(x + f\left(y + f\left(x\right)\right)\right)) \Rightarrow \left(\forall N \in \mathbb{N},\; \operatorname{step}\left(f\right)^{\left|F\right|} = \operatorname{id}\right)\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod.claim` (`✓ std3`).

*Citation.* Aoi Araoka; Tetsuji Tokihiro (2026). *Integrable Cellular Automata on Finite Fields of Order 2^n*. DOI: [10.1007/s11040-026-09569-9](https://doi.org/10.1007/s11040-026-09569-9). URL: <https://arxiv.org/abs/2602.17148v1>.

*Commentary.*

The conjecture of the paper: over a finite field of characteristic 2, for every bijective solution f of the displayed equation, which the paper shows is implied by the Yang-Baxter equation for R, and every number N of cells, the |F|-th iterate of one time step is the identity, so the period divides |F|.

**Theorem 1.5 (Proof of the conjecture).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod.result` (`✓ std3`). ∎

*Resolves.* `Problems/araoka-2026-yang-baxter-automaton-period` (proved) by `D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"araoka-2026-yang-baxter-automaton-period","declaration_gid":"D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Aoi Araoka; Tetsuji Tokihiro (2026). *Integrable Cellular Automata on Finite Fields of Order 2^n*. DOI: [10.1007/s11040-026-09569-9](https://doi.org/10.1007/s11040-026-09569-9). URL: <https://arxiv.org/abs/2602.17148v1>.

*Commentary.*

Only the additive group of F is used, and x + x = 0 for every x. Replacing f by x -> f(x + a) with f(a) = 0 gives a solution g with g(0) = 0, and then g(g(x)) = x. The involutions L_x(y) = x + g(x + y) fix x and satisfy L_(L_x(y)) L_x = L_(L_y(x)) L_y by the equation. For such a family the maps p -> p L_(p^(-1)(z)) are commuting involutions of the group P generated by the L_x, and the group they generate acts transitively on P, so P is a 2-group. The translations t_a(x) = x + a normalise P, so P together with the translations generates a 2-group Q. A nontrivial central element of Q commutes with every translation, so it is a translation t_u with u different from 0, and it commutes with g = L_0, so g(x + u) = g(x) + u and hence f(x + u) = f(x) + u. Then R commutes with adding elements of {0, u} to its inputs, so one time step commutes with adding states whose entries lie in {0, u}, and it descends to the quotient of F by {0, u}, whose order is |F|/2. By induction on the order, the |F|/2-th iterate G of one time step is the identity modulo {0, u}, so G(s) = s + d with d in {0, u} entrywise, and G(G(s)) = G(s) + d = s. Hence the |F|-th iterate is the identity.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod.carry`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod.result`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod.rmat`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod.step`
