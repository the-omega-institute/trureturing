# Unique Logarithmic Rate from Submultiplicativity

## Abstract

Every positive submultiplicative profile with a finite lower logarithmic bound has a unique asymptotic logarithmic rate.

**Theorem 1.1 (A submultiplicative profile has a unique logarithmic rate).**

$$\forall eta: \mathbb{N}\to \mathbb{R}, [(\forall n, 0< eta(n)) \land (\forall m, n, eta(m+n) \leq eta(m) \cdot eta(n)) \land \operatorname{BddBelow}(\{\frac{\log eta(n)}{n} \mid n\in \mathbb{N}\})] \Rightarrow \exists! gamma\in \mathbb{R}, \lim_{n\to\infty} \frac{\log eta(n)}{n} = gamma.$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/ContractionGeometry/SubmultiplicativeLogRate.submultiplicative_profile_has_unique_log_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking logarithms converts positivity and submultiplicativity into subadditivity. Pinned Mathlib provides Fekete's lemma as Subadditive.tendsto_lim, which gives the finite limit from the stated lower-bound hypothesis. Uniqueness follows from uniqueness of limits in the real line.

This closes only the Fekete-rate clause in source atom remark/27.684. It does not claim the atom's amplitude-damping rate values, depolarizing rate, fixed-point interpretation, or semigroup classification clauses.

## References

- Truth anchor: `D5/S3/QuantumChannels/ContractionGeometry/SubmultiplicativeLogRate.submultiplicative_profile_has_unique_log_rate`
