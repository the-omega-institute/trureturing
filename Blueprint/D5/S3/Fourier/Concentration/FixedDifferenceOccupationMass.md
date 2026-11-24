# The mass at a fixed count difference

## Abstract

A fixed signed count difference determines a shifted factorial sum.

**Theorem 1.1 (Exact mass and diagonal bound).**

$$\begin{aligned}M_{p}(a-b) = (p!)^{2} \prod_{j \in J} \left(w_{j}\right)^{a_{j}+b_{j}} R\\(\forall j \in J, 0 \leq w_{j}) \implies M_{p}(a-b) \leq C^{2} D_{p-d} c_{d}(a) c_{d}(b)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FixedDifferenceOccupationMass.fixed_difference_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be finite with real weights w. Let a and b be nonnegative integer vectors with disjoint supports and the same total degree d, with d≤p. Write M with subscript p for the total product of multinomial weights of degree-p pairs whose count difference is a−b. Write c with subscript d for the weighted multinomial coefficient of degree d and D with subscript k for the sum of their squares at degree k.

R is the sum over degree p−d vectors l of the coordinate products (w(j)²)^l(j)/(l(j)!(l(j)+a(j)+b(j))!). C denotes the binomial coefficient with parameters p and d. The inequality applies when all weights are nonnegative.

Given a pair with the prescribed difference, take its coordinatewise minimum l. The pair then equals (l+a,l+b), and every l of degree p−d gives such a pair. Disjointness of a and b turns the two coordinate factorials into l(j)! and (l(j)+a(j)+b(j))!. The weights contribute the residual power and one squared power for each common occurrence.

The factorial product for l+a dominates the products for l and a. This bounds its multinomial weight by C times the two separate weights under nonnegativity. Use the same inequality for l+b and sum the square of the common weight over the degree p−d vectors.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/FixedDifferenceOccupationMass.fixed_difference_mass`
- Dependency: [D5/S3/Fourier/Concentration/FiniteMultinomialOverlap](FiniteMultinomialOverlap.md)
