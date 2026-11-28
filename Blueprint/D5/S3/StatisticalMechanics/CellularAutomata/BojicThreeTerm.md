# Three-distinct-offset cyclic local order

## Abstract

The three-distinct-offset cyclic branch has an explicit local unipotent valuation and order.

**Theorem 1.1 (The explicit local valuation and order).**

$$\forall q \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \mathbb{N},\; \forall f \in \operatorname{Polynomial}\left(\operatorname{ZMod}\left(2\right)\right),\; \operatorname{Odd}\left(q\right) \Rightarrow \left(a < 2^{m} \cdot q \Rightarrow \left(b < 2^{m} \cdot q \Rightarrow \left(c < 2^{m} \cdot q \Rightarrow \left(a \ne b \Rightarrow \left(a \ne c \Rightarrow \left(b \ne c \Rightarrow \left(\operatorname{Monic}\left(f\right) \Rightarrow \left(\operatorname{Irreducible}\left(f\right) \Rightarrow \left(f \mid \operatorname{cycle}\left(q\right) \Rightarrow \left(\left(\neg f \mid \operatorname{trinomial}\left(a, b, c\right)\right) \Rightarrow \left(\left(\exists s \in \operatorname{Local}\left(f, m\right),\; \operatorname{IsSemisimplePart}\left(\operatorname{project}\left(f^{2^{m}}, \operatorname{trinomial}\left(a, b, c\right)\right), s\right) \land \left(\forall t \in \operatorname{Local}\left(f, m\right),\; \operatorname{IsSemisimplePart}\left(\operatorname{project}\left(f^{2^{m}}, \operatorname{trinomial}\left(a, b, c\right)\right), t\right) \Rightarrow t = s\right)\right) \land \left(\forall s \in \operatorname{Local}\left(f, m\right),\; \forall v \in \operatorname{Polynomial}\left(\operatorname{ZMod}\left(2\right)\right),\; \operatorname{IsSemisimplePart}\left(\operatorname{project}\left(f^{2^{m}}, \operatorname{trinomial}\left(a, b, c\right)\right), s\right) \Rightarrow \left(\operatorname{project}\left(f^{2^{m}}, \operatorname{trinomial}\left(a, b, c\right)\right) = s \cdot \left(1 + \operatorname{project}\left(f^{2^{m}}, v\right)\right) \Rightarrow \left(\left(\forall n \in \mathbb{N},\; n \le \operatorname{min}\left(\operatorname{preregisteredDegree}\left(f, a, b, c\right), 2^{m}\right) \Leftrightarrow \left(n \le 2^{m} \land f^{n} \mid v\right)\right) \land \operatorname{IsLeast}\left(\operatorname{SetOf}\left(\forall p \in \mathbb{N},\; \left(\exists k \in \mathbb{N},\; p = 2^{k}\right) \land \operatorname{preregisteredDegree}\left(f, a, b, c\right) \cdot p \ge 2^{m}\right), \operatorname{orderOf}\left(1 + \operatorname{project}\left(f^{2^{m}}, v\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/BojicThreeTerm.piecewise_trinomial_interface` (`✓ std3`). ∎

*Resolves.* `Problems/bojic-2026-three-term-cyclic-unipotent-order` (proved) by `D5/S3/StatisticalMechanics/CellularAutomata/BojicThreeTerm.piecewise_trinomial_interface`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bojic-2026-three-term-cyclic-unipotent-order","declaration_gid":"D5/S3/StatisticalMechanics/CellularAutomata/BojicThreeTerm.piecewise_trinomial_interface","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ana Bojić (2026). *Semisimple–Unipotent Decomposition and the Exact Order of a Linear Cellular Automaton over F2*. DOI: [10.48550/arXiv.2611.33216](https://doi.org/10.48550/arXiv.2611.33216). URL: <https://arxiv.org/abs/2611.33216v1>.

*Commentary.*

Let q be odd and let the three distinct exponents lie in the cyclic window of length 2^m q. The polynomial is the trinomial X^a + X^b + X^c over F2. For a monic irreducible factor f of X^q − 1 that does not divide this trinomial, the local quotient of thickness 2^m has a unique semisimple factor.

The dyadic case split in preregisteredDegree gives the first positive Taylor degree after removing the common power of two from the three offsets. The valuation of the unipotent factor minus one is the minimum of this degree and 2^m.

The unipotent factor has the least power-of-two order p satisfying 2^m ≤ preregisteredDegree · p. The semisimple factor and the unipotent factor multiply to the actual class in the primary quotient.

This settles the cyclic three-term direction in Section 11 for the stated distinct-offset range. Rules on other graphs are outside the statement.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/BojicThreeTerm.piecewise_trinomial_interface`
- Dependency: [D5/S3/StatisticalMechanics/CellularAutomata/BojicRule150](BojicRule150.md)
