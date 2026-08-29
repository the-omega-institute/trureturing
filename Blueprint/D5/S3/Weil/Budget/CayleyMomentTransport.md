# Cayley Moment Transport

## Abstract

Cayley moments have a finite derivative jet and a geometric scale-transport tail bound.

**Theorem 1.1 (Chebyshev-Stieltjes jet).**

$$\forall nu \in \operatorname{Measure}\left(\operatorname{Real}\left(\right)\right), n \in \operatorname{Nat}\left(\right), u \in \operatorname{Real}\left(\right), p \in \operatorname{Fin}\left(\operatorname{add}\left(n, 1\right)\right) \to \operatorname{Real}\left(\right),\; \left(0 < u \land \left(\left(\forall x \in \operatorname{Real}\left(\right),\; \operatorname{ChebyshevT}\left(\operatorname{Int}\left(\right), n, \operatorname{sub}\left(1, \operatorname{mul}\left(2, x\right)\right)\right) = \operatorname{sum}\left(\operatorname{Fin}\left(\operatorname{add}\left(n, 1\right)\right), \operatorname{lambda}\left(\operatorname{typed}\left(k, \operatorname{Fin}\left(\operatorname{add}\left(n, 1\right)\right)\right), \operatorname{mul}\left(p\left(k\right), \operatorname{pow}\left(x, k\right)\right)\right)\right)\right) \land \operatorname{Integrable}\left(\operatorname{lambda}\left(\operatorname{typed}\left(xi, \operatorname{Real}\left(\right)\right), \frac{1}{\operatorname{add}\left(\operatorname{pow}\left(xi, 2\right), u\right)}\right), nu\right)\right)\right) \Rightarrow \operatorname{integral}\left(nu, \operatorname{lambda}\left(\operatorname{typed}\left(xi, \operatorname{Real}\left(\right)\right), \frac{\operatorname{re}\left(\operatorname{pow}\left(\frac{\operatorname{add}\left(\operatorname{ofReal}\left(xi\right), \operatorname{mul}\left(\operatorname{I}\left(\right), \operatorname{sqrt}\left(u\right)\right)\right)}{\operatorname{sub}\left(\operatorname{ofReal}\left(xi\right), \operatorname{mul}\left(\operatorname{I}\left(\right), \operatorname{sqrt}\left(u\right)\right)\right)}, n\right)\right)}{\operatorname{add}\left(\operatorname{pow}\left(xi, 2\right), u\right)}\right)\right) = \operatorname{sum}\left(\operatorname{Fin}\left(\operatorname{add}\left(n, 1\right)\right), \operatorname{lambda}\left(\operatorname{typed}\left(k, \operatorname{Fin}\left(\operatorname{add}\left(n, 1\right)\right)\right), \operatorname{mul}\left(p\left(k\right), \operatorname{pow}\left(u, k\right), \frac{\operatorname{pow}\left(\operatorname{neg}\left(1\right), k\right)}{\operatorname{factorial}\left(k\right)}, \operatorname{iteratedDeriv}\left(k, \operatorname{lambda}\left(\operatorname{typed}\left(v, \operatorname{Real}\left(\right)\right), \operatorname{integral}\left(nu, \operatorname{lambda}\left(\operatorname{typed}\left(xi, \operatorname{Real}\left(\right)\right), \frac{1}{\operatorname{add}\left(\operatorname{pow}\left(xi, 2\right), v\right)}\right)\right)\right), u\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/CayleyMomentTransport.chebyshev_stieltjes_jet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The measure, positive square scale, coefficient family, polynomial identity, and resolvent integrability condition at that scale are all displayed.

The proof identifies the Cayley real part with the shifted Chebyshev polynomial and differentiates the resolvent integral under a locally dominated integral.

**Theorem 1.2 (Budget transport error).**

$$\forall nu \in \operatorname{Measure}\left(\operatorname{Real}\left(\right)\right), a \in \operatorname{Real}\left(\right), b \in \operatorname{Real}\left(\right), M \in \operatorname{Nat}\left(\right),\; \left(0 < a \land \left(0 < b \land \operatorname{Integrable}\left(\operatorname{lambda}\left(\operatorname{typed}\left(xi, \operatorname{Real}\left(\right)\right), \frac{1}{\operatorname{add}\left(\operatorname{pow}\left(xi, 2\right), \operatorname{pow}\left(a, 2\right)\right)}\right), nu\right)\right)\right) \Rightarrow \operatorname{abs}\left(\operatorname{sub}\left(\operatorname{integral}\left(nu, \operatorname{lambda}\left(\operatorname{typed}\left(xi, \operatorname{Real}\left(\right)\right), \frac{1}{\operatorname{add}\left(\operatorname{pow}\left(xi, 2\right), \operatorname{pow}\left(b, 2\right)\right)}\right)\right), \operatorname{mul}\left(\frac{a}{b}, \operatorname{add}\left(\operatorname{integral}\left(nu, \operatorname{lambda}\left(\operatorname{typed}\left(xi, \operatorname{Real}\left(\right)\right), \frac{1}{\operatorname{add}\left(\operatorname{pow}\left(xi, 2\right), \operatorname{pow}\left(a, 2\right)\right)}\right)\right), \operatorname{mul}\left(2, \operatorname{sum}\left(\operatorname{range}\left(M\right), \operatorname{lambda}\left(\operatorname{typed}\left(k, \operatorname{Nat}\left(\right)\right), \operatorname{mul}\left(\operatorname{pow}\left(\operatorname{neg}\left(\frac{\operatorname{sub}\left(a, b\right)}{\operatorname{add}\left(a, b\right)}\right), \operatorname{add}\left(k, 1\right)\right), \operatorname{integral}\left(nu, \operatorname{lambda}\left(\operatorname{typed}\left(xi, \operatorname{Real}\left(\right)\right), \frac{\operatorname{re}\left(\operatorname{pow}\left(\frac{\operatorname{add}\left(\operatorname{ofReal}\left(xi\right), \operatorname{mul}\left(\operatorname{I}\left(\right), a\right)\right)}{\operatorname{sub}\left(\operatorname{ofReal}\left(xi\right), \operatorname{mul}\left(\operatorname{I}\left(\right), a\right)\right)}, \operatorname{add}\left(k, 1\right)\right)\right)}{\operatorname{add}\left(\operatorname{pow}\left(xi, 2\right), \operatorname{pow}\left(a, 2\right)\right)}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \le \operatorname{mul}\left(\frac{\operatorname{mul}\left(2, a\right)}{b}, \operatorname{integral}\left(nu, \operatorname{lambda}\left(\operatorname{typed}\left(xi, \operatorname{Real}\left(\right)\right), \frac{1}{\operatorname{add}\left(\operatorname{pow}\left(xi, 2\right), \operatorname{pow}\left(a, 2\right)\right)}\right)\right), \frac{\operatorname{pow}\left(\operatorname{abs}\left(\frac{\operatorname{sub}\left(a, b\right)}{\operatorname{add}\left(a, b\right)}\right), \operatorname{add}\left(M, 1\right)\right)}{\operatorname{sub}\left(1, \operatorname{abs}\left(\frac{\operatorname{sub}\left(a, b\right)}{\operatorname{add}\left(a, b\right)}\right)\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/CayleyMomentTransport.budget_transport_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two positive scales, truncation order, measure, and resolvent integrability premise are displayed explicitly.

The proof expands every moment from the Cayley coordinate, reduces scale transport to the Poisson kernel, and integrates its finite geometric remainder.

## References

- Truth anchor: `D5/S3/Weil/Budget/CayleyMomentTransport.budget_transport_error`
- Truth anchor: `D5/S3/Weil/Budget/CayleyMomentTransport.chebyshev_stieltjes_jet`
