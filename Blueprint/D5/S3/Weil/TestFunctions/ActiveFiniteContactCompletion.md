# Active Finite-Contact Completion

## Abstract

Positive active pressure produces an exact finite-contact completion.

**Theorem 1.1 (Active pressure gives a finite atomic completion).**

$$\forall d \in \operatorname{Nat}\left(\right), a \in \operatorname{Real}\left(\right), theta \in \operatorname{Real}\left(\right), alpha \in \operatorname{NNReal}\left(\right), phi \in \operatorname{WeilTestFunction}\left(\right), observer \in \operatorname{Fin}\left(d\right) \to \operatorname{WeilTestFunction}\left(\right), sigma \in \operatorname{FiniteMeasure}\left(\operatorname{Circle}\left(\right)\right),\; \left(0 < a \land \left(0 < theta \land \left(\left(\forall i \in \operatorname{Fin}\left(d\right), x \in \operatorname{Real}\left(\right),\; \operatorname{conj}\left(observer\left(i\right)\left(x\right)\right) = observer\left(i\right)\left(x\right)\right) \land \operatorname{support}\left(sigma\right) \subseteq \left\{\operatorname{cayleyMomentFunction}\left(a, phi, z\right) + theta = 0 \mid z \in \operatorname{Circle}\left(\right)\right\}\right)\right)\right) \Rightarrow \left(\exists I \in Type, finiteI \in \operatorname{Fintype}\left(I\right), point \in I \to \operatorname{Circle}\left(\right), weight \in I \to \operatorname{Real}\left(\right), muStar \in \operatorname{Measure}\left(\operatorname{Circle}\left(\right)\right),\; \operatorname{card}\left(I\right) \le d + 1 \land \left(\left(\forall r \in I,\; 0 < weight\left(r\right)\right) \land \left(\left(\forall r \in I,\; \operatorname{cayleyMomentFunction}\left(a, phi, point\left(r\right)\right) + theta = 0\right) \land \left(\left(\forall r \in I,\; \operatorname{cayleyMomentFunction}\left(a, phi, \operatorname{inv}\left(point\left(r\right)\right)\right) + theta = 0\right) \land \left(\operatorname{sum}\left(r, I, weight\left(r\right)\right) = \operatorname{measureReal}\left(sigma, \operatorname{univ}\left(\operatorname{Circle}\left(\right)\right)\right) \land \left(muStar = \operatorname{smul}\left(alpha, \operatorname{normalizedCircleHaar}\left(\right)\right) + \operatorname{sum}\left(r, I, \operatorname{smul}\left(\operatorname{ofReal}\left(weight\left(r\right)\right), \operatorname{dirac}\left(point\left(r\right)\right)\right)\right) \land \left(\forall i \in \operatorname{Fin}\left(d\right),\; \operatorname{integral}\left(z, \operatorname{Circle}\left(\right), \operatorname{cayleyMomentFunction}\left(a, observer\left(i\right), z\right), \operatorname{sum}\left(r, I, \operatorname{smul}\left(\operatorname{ofReal}\left(weight\left(r\right)\right), \operatorname{dirac}\left(point\left(r\right)\right)\right)\right)\right) = \operatorname{integral}\left(z, \operatorname{Circle}\left(\right), \operatorname{cayleyMomentFunction}\left(a, observer\left(i\right), z\right), sigma\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/ActiveFiniteContactCompletion.active_finite_contact_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite residual supported on the active KKT contact set can be replaced by positive contact atoms while retaining its mass and every moment in the supplied real observer family.

The completion keeps the same nonnegative Haar coefficient, uses at most d plus one atoms, and every chosen contact has an inverse contact, so the support is indexed by at most d plus one conjugate contact orbits.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/ActiveFiniteContactCompletion.active_finite_contact_completion`
- Dependency: [D5/S3/Weil/TestFunctions/CayleyMomentTransport](CayleyMomentTransport.md)
