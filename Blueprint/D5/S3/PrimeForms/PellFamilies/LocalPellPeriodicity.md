# Local Periodicity of Pell Recurrences

## Abstract

Pell-unit and unimodular recurrences are pure-periodic under every prime-power observation.

**Theorem 1.1 (Pell recurrences are periodic modulo every prime power).**

$$\forall D, x, y \in \mathbb{Z}, s, t: \operatorname{Fin}\left(2\right) \to \mathbb{Z},\\{}G: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{Z}\right), p, k \in \mathbb{N}, \operatorname{Prime}\left(p\right)\\{}\Rightarrow \operatorname{let} q = {p}^{{k}}, R = (M \mapsto \operatorname{mod}\left(M, q\right)),\\{}r = (v \mapsto (i \mapsto \operatorname{mod}\left(v_{i}, q\right))), U = \operatorname{Matrix2}\left(x, D y, y, x\right),\\{}u = (n \mapsto {\operatorname{R}\left(U\right)}^{{n}} \operatorname{r}\left(s\right)), z = (n \mapsto {\operatorname{R}\left(G\right)}^{{n}} \operatorname{r}\left(t\right))\;\\{}(({x}^{{2}} - D {y}^{{2}} = 1 \lor {x}^{{2}} - D {y}^{{2}} = -1) \Rightarrow \exists T \in \mathbb{N}, 0 < T \land \forall n \in \mathbb{N}, u_{n+T} = u_{n}) \land\\{}((\operatorname{det}\left(G\right) = 1 \lor \operatorname{det}\left(G\right) = -1) \Rightarrow \exists T \in \mathbb{N}, 0 < T \land \forall n \in \mathbb{N}, z_{n+T} = z_{n}).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PellFamilies/LocalPellPeriodicity.pell_unit_and_unimodular_recurrences_are_locally_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a prime p and an exponent k. The observer modulus is q = p^k. The displayed reduction maps act entrywise on integral two-by-two matrices and two-coordinate integer states.

For an integral Pell unit x + y sqrt(D), multiplication on its two coordinates is the explicit matrix with rows (x, Dy) and (y, x). Its determinant is x^2 - D y^2, so norm one or minus one makes its reduction invertible. The first implication therefore gives a positive pure period for its observed orbit.

The second implication treats an arbitrary integral unimodular two-coordinate recurrence independently. Reduction preserves the unit determinant, and the reduced matrix belongs to a finite unit group. Its positive finite order is a period from time zero for every reduced seed.

## References

- Truth anchor: `D5/S3/PrimeForms/PellFamilies/LocalPellPeriodicity.pell_unit_and_unimodular_recurrences_are_locally_periodic`
- Dependency: [D5/S3/PrimeForms/PellFamilies/CrossingPellFamily](CrossingPellFamily.md)
- Dependency: [D5/S3/PrimeForms/PellFamilies/SqrtTwentyOnePellTower](SqrtTwentyOnePellTower.md)
