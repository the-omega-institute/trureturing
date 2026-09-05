# Hecke Pole Lattice

## Abstract

A Hecke-type factor is meromorphic on the plane with an exact regulator-spaced pole lattice.

**Theorem 1.1 (The Hecke factor has exactly the regulator-spaced simple poles).**

$$\begin{aligned}eta>1, \operatorname{P}\left(k, s\right) := {1 - \operatorname{exp}\left((s + 2\times k) \log eta\right)}^{-1},\\\forall k \in \mathbb{N}, \operatorname{MeromorphicOn}\left(P_{k}, \mathbb{C}\right) \land\\\forall s \in \mathbb{C}, \operatorname{meromorphicOrderAt}\left(P_{k}, s\right) = -1 \iff \exists n \in \mathbb{Z}, s = -2\times k + \frac{2\pi i n}{\log eta}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HeckePoleLattice.hecke_pole_lattice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For eta greater than one, define the k-th Hecke factor as the reciprocal of 1 minus exp((s+2k) log eta). The denominator is entire, so its reciprocal is meromorphic on the whole complex plane.

The complex exponential equals one exactly at integer multiples of 2 pi i. Since log eta is positive and nonzero, solving the resulting linear equation gives precisely -2k + 2 pi i n / log eta. The integer n includes both signs in the source notation.

At every denominator zero its derivative is -log eta, hence nonzero. Mathlib's analytic-order criterion gives denominator order one, and the inverse-order law gives factor order minus one. Away from the lattice the order is zero, proving the displayed biconditional.

This formalizes the exact pole mechanism of the source Hecke grid. It does not identify the source's Beatty-Dirichlet series with this factor without an independently supplied analytic factorization.

## References

- Truth anchor: `D5/S3/Analytic/HeckePoleLattice.hecke_pole_lattice`
