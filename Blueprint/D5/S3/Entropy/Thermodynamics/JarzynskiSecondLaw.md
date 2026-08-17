# Jarzynski Equality and the Second Law

## Abstract

The Jarzynski equality at positive inverse temperature bounds free-energy change by mean work.

**Theorem 1.1 (Jarzynski equality implies the mean-work bound).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, W: \iota\to \mathbb{R},\\\forall \beta, \Delta F\in \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum_{i}p(i)=1 \land 0< \beta \land \\\sum_{i}p(i) \exp{-\beta W(i)}=\exp{-\beta \Delta F}) \Rightarrow\\\Delta F \le \sum_{i}p(i) W(i).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Thermodynamics/JarzynskiSecondLaw.jarzynski_implies_second_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a nonnegative normalized mass function on a finite type and let W be the work value in each outcome. The hypothesis is the Jarzynski equality written directly with the free-energy difference, so no partition-function definition is introduced.

The proof applies Mathlib's finite weighted Jensen inequality for the convex real exponential. The resulting exponential inequality is reflected to an inequality between its exponents, and positivity of beta reverses the negative scaling to give the mean-work bound.

This theorem closes only the implication from the stated Jarzynski equality to the second-law inequality. It does not formalize the atom's separate claims about Crooks fluctuations, Spohn monotonicity, thermodynamic length, or numerical residuals.

## References

- Truth anchor: `D5/S3/Entropy/Thermodynamics/JarzynskiSecondLaw.jarzynski_implies_second_law`
