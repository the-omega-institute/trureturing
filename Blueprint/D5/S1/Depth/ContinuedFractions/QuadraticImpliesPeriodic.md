# Bounded Complete Quotients Force Periodicity

## Abstract

Uniformly bounded integral quadratic certificates reduce complete quotients to a finite state space and force eventual periodicity.

**Lemma 1.1 (A nonzero coefficient triple gives a nonzero polynomial).**

$$\forall u \in \mathbb{Z}^{3}, u \neq (0, 0, 0) \Rightarrow \operatorname{quadraticPolynomial}\left(u\right) \neq 0.$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/QuadraticImpliesPeriodic.quadraticPolynomial_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An integral triple (a,b,c) encodes the real polynomial a t^2+b t+c. If the encoded polynomial vanished identically, its coefficients in degrees two, one, and zero would all vanish, contradicting the assumption that the triple is nonzero.

This is a statement about the polynomial itself. It does not assert irreducibility, degree exactly two, or the existence of a root.

**Theorem 1.2 (Bounded complete quotients force eventual periodicity).**

$$\forall x \in \mathbb{R}, (\operatorname{IsQuadraticIrrational}\left(x\right) \land \operatorname{BoundedCompleteQuotientCertificate}\left(x\right)) \Rightarrow \exists s \in \mathbb{N}, \exists p \in \mathbb{N}, 0 < p \land \forall k \in \mathbb{N}, \operatorname{coefficient}\left(x, s + k + p\right) = \operatorname{coefficient}\left(x, s + k\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/QuadraticImpliesPeriodic.quadratic_irrational_eventually_periodic_of_bounded_complete_quotients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume x is a quadratic irrational and every complete quotient of x satisfies a nonzero integral quadratic whose three coefficients share one uniform bound. Only finitely many coefficient triples can then occur, and each corresponding nonzero polynomial has only finitely many real roots. The complete quotients therefore range over a finite set.

Two complete quotients must consequently coincide. The shift lemma turns that repeated state into a positive period for every later continued-fraction coefficient. The bounded certificate is an explicit hypothesis here: this module does not prove that every quadratic irrational supplies such a uniform bound.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/QuadraticImpliesPeriodic.quadraticPolynomial_ne_zero`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/QuadraticImpliesPeriodic.quadratic_irrational_eventually_periodic_of_bounded_complete_quotients`
