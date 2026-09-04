# Finite Ritz--Christoffel Bounds

## Abstract

A positive top-atom mass and spectral gap convert an attained reduced-energy minimum into a sharp two-sided variational Ritz error bar.

**Theorem 1.1 (Sharp finite variational error bar).**

$$\forall Trial \in Type, mu1 \in \mathbb{R}, g \in \mathbb{R}, lambda \in \mathbb{R}, epsilon \in \mathbb{R}, T \in Trial \to \mathbb{R}, E \in Trial \to \mathbb{R},\; \left(0 < mu1 \land \left(0 < g \land \left(\left(\forall q \in Trial,\; 0 \le T\left(q\right) \land \left(0 \le E\left(q\right) \land g \cdot T\left(q\right) \le E\left(q\right)\right)\right) \land \left(\operatorname{IsLeast}\left(\operatorname{range}\left(E\right), lambda\right) \land \operatorname{IsLeast}\left(\operatorname{range}\left((q \mapsto \frac{E\left(q\right)}{mu1 + T\left(q\right)})\right), epsilon\right)\right)\right)\right)\right) \Rightarrow \left(delta = \frac{lambda}{mu1 \cdot g} \land \left(\left(0 \le delta \land \left(\frac{lambda}{mu1 \cdot {1 + delta}} \le epsilon \land epsilon \le \frac{lambda}{mu1}\right)\right) \land \left(\frac{lambda}{mu1 + 0} = \frac{lambda}{mu1} \land \frac{lambda}{mu1 + \frac{lambda}{g}} = \frac{lambda}{mu1 \cdot {1 + delta}}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/FiniteRitzChristoffelBounds.finite_ritz_christoffel_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The atom mass and spectral gap are explicitly positive. Tail mass and reduced energy are nonnegative, and the gap times tail mass is bounded by reduced energy for every trial.

Attainment of both minima avoids any total-infimum convention. Comparing denominators gives the lower error bar; evaluating the Ritz minimum at a Christoffel minimizer gives the upper bar. The two final scalar configurations attain its two endpoints.

The source's zeta-specific superfactorial rate is not part of this statement: it requires additional zero-density and orthogonal-polynomial asymptotics.

## References

- Truth anchor: `D5/S3/Analytic/FiniteRitzChristoffelBounds.finite_ritz_christoffel_bounds`
