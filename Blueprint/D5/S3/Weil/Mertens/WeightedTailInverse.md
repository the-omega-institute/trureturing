# A positive inverse with only an L1 premise

## Abstract

Positive logarithmic weighted-tail inversion for arbitrary real L1 kernels

Use the existing tail(k,x)=integral_(x,infinity) k(t) dt and weightedTail(k,x)=integral_(x,infinity) k(t)*r(t) dt, where r(t)=(1+log(t))/log(t)^2. Set a(t)=log(t)^2/(1+log(t)) and v(t)=log(t)*(log(t)+2)/(t*(1+log(t))^2). On t>1, v=a' is nonnegative and r*a=1. Neither v nor its half-line integral is assumed integrable. All integrals use Lebesgue volume.

**Definition 1.1 (The reciprocal logarithmic weight).**

$$\forall t \in \mathbb{R},\; \operatorname{a}\left(t\right) = \frac{\operatorname{log}\left(t\right)^{2}}{1 + \operatorname{log}\left(t\right)}$$

*Formalization.* `D5/S3/Weil/Mertens/WeightedTailInverse.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition is totalized on Real; positivity and the reciprocal identity are used only at t>1.

**Definition 1.2 (The positive derivative density).**

$$\forall t \in \mathbb{R},\; \operatorname{v}\left(t\right) = \frac{\operatorname{log}\left(t\right) \cdot \left(\operatorname{log}\left(t\right) + 2\right)}{t \cdot \left(1 + \operatorname{log}\left(t\right)\right)^{2}}$$

*Formalization.* `D5/S3/Weil/Mertens/WeightedTailInverse.v` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This derivative density is nonnegative on t>1; only finite interval integrability is used before triangular absolute Fubini.

**Theorem 1.3 (Absolute Fubini proves the positive inverse).**

$$\forall k \in \mathbb{R} \to \mathbb{R},\; \forall x \in \mathbb{R},\; 2 \le x \Rightarrow \left(\operatorname{IntegrableOn}\left(k, \operatorname{Ioi}\left(x\right)\right) \Rightarrow \left(\operatorname{IntegrableOn}(t\mapsto\operatorname{v}\left(t\right) \cdot \operatorname{weightedTail}\left(k, t\right),\operatorname{Ioi}\left(x\right)) \land \operatorname{tail}\left(k, x\right) = \operatorname{a}\left(x\right) \cdot \operatorname{weightedTail}\left(k, x\right) + \int_{x < t}\operatorname{v}\left(t\right) \cdot \operatorname{weightedTail}\left(k, t\right)\,dt\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/WeightedTailInverse.inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each endpoint u>x, truncate v to (x,u). Its mass is a(u)-a(x), and 0<=r(u)*(a(u)-a(x))<=1. Hence the norm integral of the triangular kernel is bounded by |k(u)|. Absolute Fubini pays both the exchanged integral and integrability of v*weightedTail. No boundary limit, extra moment, or sign premise on k is used.

**Theorem 1.4 (A closed-tail weighted lower bound controls the unweighted tail).**

$$\forall k \in \mathbb{R} \to \mathbb{R},\; \forall x \in \mathbb{R},\; \forall A \in \mathbb{R},\; \operatorname{exp}\left(1\right) \le x \Rightarrow \left(0 \le A \Rightarrow \left(\operatorname{IntegrableOn}\left(k, \operatorname{Ioi}\left(x\right)\right) \Rightarrow \left(\left(\forall t \in \mathbb{R},\; x \le t \Rightarrow \frac{-A}{\operatorname{sqrt}\left(t\right) \cdot \operatorname{log}\left(t\right)} \le \operatorname{weightedTail}\left(k, t\right)\right) \Rightarrow \frac{-\left(3 \cdot A\right)}{\operatorname{sqrt}\left(x\right)} \le \operatorname{tail}\left(k, x\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/WeightedTailInverse.tail_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x>=exp(1) and A>=0, assume the weighted bound at every t>=x, including x. The endpoint contribution is at least -A/sqrt(x). Since v(t)/(sqrt(t)*log(t))<=t^(-3/2), the integral contribution is at least -2*A/sqrt(x). The inverse gives the stated -3*A/sqrt(x) lower bound. The kernel remains arbitrary real L1.

## References

- Truth anchor: `D5/S3/Weil/Mertens/WeightedTailInverse.a`
- Truth anchor: `D5/S3/Weil/Mertens/WeightedTailInverse.inverse`
- Truth anchor: `D5/S3/Weil/Mertens/WeightedTailInverse.tail_lower_bound`
- Truth anchor: `D5/S3/Weil/Mertens/WeightedTailInverse.v`
- Dependency: [D5/S3/Weil/Mertens/WeightedTailTransport](WeightedTailTransport.md)
