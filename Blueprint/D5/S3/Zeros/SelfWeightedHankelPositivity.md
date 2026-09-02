# Finite Self-Weighted Hankel Positivity

## Abstract

A finite self-weighted Hankel quadratic form is exactly a sum of weighted polynomial norm squares.

**Theorem 1.1 (The self-weighted Hankel form has an exact norm-square expansion).**

$$\begin{aligned}\forall R \mathrm{finite}, N \in \mathbb{N}, m, v: R \to \mathbb{R},\\c: \operatorname{Fin}(N + 1) \to \mathbb{C},\\\sum_{i = 0}^{N} \sum_{j = 0}^{N} \overline{c_{i}} c_{j} \sum_{r \in R} m_{r} v_{r}^{i + j + 1} = \sum_{r \in R} m_{r} v_{r} \left|\sum_{k = 0}^{N} c_{k} v_{r}^{k}\right|^{2}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/SelfWeightedHankelPositivity.selfWeightedHankel_quadraticForm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be a finite node set, with real multiplicities m and real nodes v. The matrix is built as the sum of rank-one monomial Gram matrices, where node r carries the source-prescribed weight m(r)v(r). Its (i,j) entry is therefore the shifted moment sum of m(r)v(r)^(i+j+1).

For every complex coefficient vector c, the corresponding quadratic form is the sum over r of m(r)v(r) times the squared modulus of the polynomial evaluated at v(r). Nonnegative multiplicities and nodes make the matrix positive semidefinite; one positive-weight node with nonzero evaluation makes that particular quadratic form strictly positive.

This finite theorem is the algebraic core of the proposed Hamburger criterion. It does not assert the source's RH equivalence: the reverse direction needs a Hamburger representation theorem and meromorphic continuation machinery that are not present in the formal library.

## References

- Truth anchor: `D5/S3/Zeros/SelfWeightedHankelPositivity.selfWeightedHankel_quadraticForm`
