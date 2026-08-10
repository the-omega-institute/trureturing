# The Effective Hurwitz Bound at the Golden Ratio

## Abstract

No rational lies within one over root-five den squared plus den of the golden ratio.

**Theorem 1.1 (Every rational keeps quantified distance from the golden ratio).**

$$\forall q\in \mathbb{Q},\ \frac{1}{\sqrt{5}\,\operatorname{den}(q)^{2}+\operatorname{den}(q)} < |\varphi-q|$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/GoldenHurwitzBound.golden_hurwitz_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the uniform, fully effective form of the badly-approximable property of the golden ratio, with the sharp constant of Hurwitz's classical approximation theorem appearing explicitly. Hurwitz's theorem says every irrational admits infinitely many rationals within one over root-five den squared, and that at the golden ratio the constant root five cannot be improved. The deposited statement is the complementary uniform lower bound: no rational at all, convergent or not, comes within one over root-five den squared plus den of the golden ratio. The first-order term of the denominator is the sharp root-five den squared; the additive den absorbs the second-order error uniformly, so the bound holds for every denominator down to one.

The proof is the classical quadratic-form argument, carried out natively over pinned mathlib. The integer form num squared minus num times den minus den squared vanishes at no rational, since a rational zero would make a root of the golden polynomial rational, contradicting the irrationality of both golden roots; hence the form has absolute value at least one. Factoring it through the two roots writes this certificate as den squared times the distance to the golden ratio times the distance to its conjugate, and the triangle inequality caps the conjugate distance by the golden distance plus root five. Excluding the contrary bound is then elementary real arithmetic.

Pinned mathlib has Dirichlet's approximation theorem and the Legendre convergent criterion but no Hurwitz-type bound and no badly-approximable machinery, so the theorem is a new proof rather than a wrapper. The sharpness side lives in the sibling module on Fibonacci convergent errors, whose exact error ratios exhibit the approach to the root-five constant along the convergents of the golden continued fraction. No Lagrange spectrum, no Markov chain of worst constants, and no statement for other quadratic irrationals is claimed.

## References

- Truth anchor: `D5/S1/Depth/GoldenHurwitzBound.golden_hurwitz_bound`
