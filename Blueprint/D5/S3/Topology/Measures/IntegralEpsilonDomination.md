# Integral convergence under epsilon domination

## Abstract

Integral convergence with epsilon-dependent controls on arbitrary measure spaces.

The universe u and measurable space Omega are arbitrary. The measure mu need not be finite or sigma-finite. The sequence f has type Nat -> Omega -> Real. The bound M is a real number; nonnegativity follows from the control premise. For each positive epsilon, a has type Nat -> Omega -> Real and b has type Omega -> Real; both may depend on epsilon. AE(mu,P) means that P holds mu-almost everywhere, Integrable means real Bochner integrability, and integral(mu,h) is the real Bochner integral of h.

**Theorem 1.1 (A common integral budget with varying pointwise controls).**

$$\begin{aligned}\forall Omega: Type_{u}, [\operatorname{MeasurableSpace}\left(Omega\right)]\\\forall mu: \operatorname{Measure}\left(Omega\right), \forall f: Nat \to Omega \to Real, \forall M: Real, \\(\forall n: Nat, \operatorname{Integrable}\left(f(n), mu\right)) \Rightarrow\\\operatorname{AE}\left(mu, (x \mapsto \operatorname{Tendsto}\left((n \mapsto f(n)(x)), atTop, \operatorname{nhds}\left(0\right)\right))\right) \Rightarrow\\(\forall n: Nat, \forall x: Omega, 0 \leq f(n)(x)) \Rightarrow\\(\forall epsilon: Real, 0 < epsilon \Rightarrow\\\exists a: Nat \to Omega \to Real, \exists b: Omega \to Real, \\(\forall n: Nat, \operatorname{Integrable}\left(a(n), mu\right)) \land \operatorname{Integrable}\left(b, mu\right)\\\land (\forall n: Nat, \forall x: Omega, 0 \leq a(n)(x))\\\land (\forall x: Omega, 0 \leq b(x))\\\land (\forall n: Nat, \operatorname{integral}\left(mu, a(n)\right) \leq M)\\\land (\forall n: Nat, \forall x: Omega, f(n)(x) \leq epsilon a(n)(x) + b(x))) \Rightarrow\\\operatorname{Tendsto}\left((n \mapsto \operatorname{integral}\left(mu, f(n)\right)), atTop, \operatorname{nhds}\left(0\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/IntegralEpsilonDomination.tendsto_integral_of_epsilon_domination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every f(n) is integrable and pointwise nonnegative, and f(n,x) tends to zero almost everywhere. For every epsilon > 0 there are nonnegative integrable controls a(n) and b such that f(n,x) <= epsilon a(n,x) + b(x) for every n and x, with integral(a(n)) <= M. The same finite M works for all epsilon and n. Then the integrals of f(n) tend to zero.

Fix epsilon and truncate to F(n,x) = max(f(n,x) - epsilon a(n,x),0). The inequalities 0 <= F(n,x) <= f(n,x) give almost-everywhere convergence to zero. The fixed-epsilon bound F(n,x) <= b(x) supplies dominated convergence. The remaining integral is at most epsilon M, so letting epsilon decrease proves the result. No pointwise convergence of a(n), common choice of a or b across epsilon, or uniform bound on integral(b) across epsilon is assumed.

This isolates the classical truncation argument used in Brézis–Lieb splitting. Both nonlinear complex cancellation and positive-power splitting follow by applying this criterion to the norm of the corresponding defect. No mathematical originality is claimed.

## References

- Truth anchor: `D5/S3/Topology/Measures/IntegralEpsilonDomination.tendsto_integral_of_epsilon_domination`
