# Jarzynski Equality Implies the Mean-Work Bound

## Abstract

For a finite probability law, the Jarzynski equality implies the mean-work lower bound by convexity of the exponential.

**Theorem 1.1 (The exponential equality casts the second-law inequality).**

$$\begin{gathered}\forall \iota, s\in \operatorname{Finset}(\iota),\\\forall p, W: \iota\to \mathbb{R}, \beta, \Delta F\in \mathbb{R},\\(\forall i\in s, 0\le p(i)) \land \sum_{i\in s} p(i) = 1 \land 0< \beta \land\\\sum_{i\in s} p(i) \exp (-\beta W(i)) = \exp (-\beta \Delta F) \Rightarrow\\\Delta F \le \sum_{i\in s} p(i) W(i).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/Thermodynamics/JarzynskiSecondLaw.jarzynski_implies_mean_work_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be nonnegative and normalized on the finite set s, let beta be positive, and suppose the weighted exponential work average is exactly exp(-beta times the free-energy difference). Convexity of the exponential puts exp(-beta times mean work) below that average. Strict monotonicity of exp and positivity of beta then give the displayed mean-work lower bound.

The Lean proof applies Mathlib's finite weighted Jensen theorem ConvexOn.map_sum_le to convexOn_exp. It formalizes only the Jarzynski-to-mean-work implication; no Crooks relation, fluctuation model, or open-system monotonicity claim is included.

## References

- Truth anchor: `D5/S3/DivergenceSupport/Thermodynamics/JarzynskiSecondLaw.jarzynski_implies_mean_work_lower_bound`
