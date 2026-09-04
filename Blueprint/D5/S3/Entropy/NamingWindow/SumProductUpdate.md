# Coordinate Sum-Product Update

## Abstract

A public, commutative-semiring form of the coordinate sum-product identity.

**Theorem 1.1 (A distinguished coordinate factors from the assignment sum).**

$$\begin{gathered}\forall iota: Type, [\operatorname{Fintype}\left(iota\right)], [\operatorname{DecidableEq}\left(iota\right)],\\\forall O: Type, [\operatorname{Fintype}\left(O\right)],\\\forall R: Type, [\operatorname{CommSemiring}\left(R\right)],\\\forall p: iota \to O \to R, i: iota, g: O \to R,\\\sum_{u: iota \to O} {\prod_{j \in \operatorname{erase}\left(univ, i\right)} p\left(j\right)\left(u\left(j\right)\right)} \times g\left(u\left(i\right)\right) = {\prod_{j \in \operatorname{erase}\left(univ, i\right)} \sum_{a: O} p\left(j\right)\left(a\right)} \times \sum_{a: O} g\left(a\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/SumProductUpdate.sum_prod_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing over every assignment the product of all coordinates except one, times a factor at that one coordinate, factors into the product of the other coordinates' sums times the sum of that factor.

The value here is an API one, not mathematical novelty. The identity follows from the distributive law for finite products of sums; what the repository lacked was a public name for it.

Three frozen modules in this directory each carry a private copy of this exact statement. Two record in their headers that they re-prove it because the earlier copies are "private and not reusable public theorems". Those three are frozen and therefore cannot import this module: naming the fact here does not remove them; it stops the next copy.

The frozen copies fix the codomain to the reals, while the argument needs no subtraction, division, or order. The public statement is therefore given over an arbitrary commutative semiring.

## References

- Truth anchor: `D5/S3/Entropy/NamingWindow/SumProductUpdate.sum_prod_update`
