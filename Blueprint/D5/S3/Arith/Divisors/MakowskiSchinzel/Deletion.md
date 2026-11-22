# Deletion products and reciprocal mass

## Abstract

Deletion products and reciprocal mass

**Theorem 1.1 (A geometric majorant for a finite product).**

$$\forall S \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall x \in \mathbb{N} \to \mathbb{Q},\; \forall t \in \mathbb{Q},\; \left(\forall i \in \mathbb{N},\; i \in S \Rightarrow 0 \le \operatorname{x}\left(i\right)\right) \Rightarrow \left(\sum_{i \in S} (\operatorname{x}\left(i\right)) \le t \Rightarrow \left(\prod_{i \in S} (1 + \operatorname{x}\left(i\right)) \le \sum_{j \in \operatorname{range}\left(\operatorname{card}\left(S\right) + 1\right)} (t^{j}) \land \left(\prod_{i \in S} (1 + \operatorname{x}\left(i\right)) = \sum_{j \in \operatorname{range}\left(\operatorname{card}\left(S\right) + 1\right)} (t^{j}) \Leftrightarrow \left(\operatorname{card}\left(S\right) = 0 \lor \left(t = 0 \lor \left(\operatorname{card}\left(S\right) = 1 \land \sum_{i \in S} (\operatorname{x}\left(i\right)) = t\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/Deletion.prod_one_add_le_geom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

Nonnegative increments with total at most t have product of 1+x bounded by the finite geometric sum through the size of the set. Equality holds exactly when the set is empty, t=0, or the set is a singleton whose increment equals t. Negative increments cannot be allowed uniformly: x=-3 on a two-element set and t=0 give product 4 and geometric sum 1.

**Theorem 1.2 (The strict necessary mass inequality).**

$$\forall r \in \mathbb{N},\; 0 < r \Rightarrow \left(\forall Q \in \operatorname{Finset}\left(\mathbb{N}\right),\; \operatorname{geom}\left(r, \operatorname{card}\left(Q\right)\right) < \prod_{q \in Q} (\frac{q}{q - 1}) \Rightarrow 1 < \sum_{q \in Q} (\frac{r}{q - 1})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/Deletion.necessary_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

If a deletion product exceeds its geometric factor at a positive r, the sum of r/(q-1) must exceed 1. This conclusion is strict. The deletion inequality itself forces every q to exceed 1: q=0 or q=1 would make the product zero. No separate denominator hypothesis is needed. Positivity of r is necessary: r=0 and Q={2} give deletion product 2 above geometric factor 1, but reciprocal mass 0.

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/Deletion.necessary_mass`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/Deletion.prod_one_add_le_geom`
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction](Reduction.md)
