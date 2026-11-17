# Evaluated Euler cancellation certificates

## Abstract

A finite algebraic cancellation identity controls one entire family of analytic prime remainders.

**Theorem 1.1 (Uniform analytic evaluation of a finite certificate).**

$$\begin{aligned}\forall J,I,T: \operatorname{Type}(), [\operatorname{Fintype}(J)][\operatorname{Fintype}(I)][\operatorname{Fintype}(T)],\\\forall d:\operatorname{Data}(J, I, T), \forall N\in \mathbb{N},\\\operatorname{Certificate}(d) \land (\forall i\in I, 1\leq \operatorname{deg}(\operatorname{mode}(d, i))) \land (\forall t\in T, N+1\leq \operatorname{deg}(\operatorname{tailMode}(d, t))) \implies\\\forall b:J\Rightarrow\mathbb{R}, \forall m,e,A\in \mathbb{R},\\0<m \land (\forall j\in J, m\leq \operatorname{b}(j)) \land 0<e \land 0\leq A \land 2\leq (N+1)em \implies\\\exists C\in \mathbb{R}, 0\leq C \land \forall R:\operatorname{Primes}()\Rightarrow\mathbb{C}\Rightarrow\mathbb{C},\\(\forall p\in \operatorname{Primes}(), \operatorname{Analytic}(\operatorname{R}(p), \operatorname{H}(e))) \land (\forall p\in \operatorname{Primes}(), \forall s\in \operatorname{H}(e), \operatorname{norm}(\operatorname{R}(p, s))\leq A\frac{1}{p^{2}}) \implies\\\forall p\in \operatorname{Primes}(), \operatorname{Analytic}(\operatorname{K}(d, b, R, p), \operatorname{H}(e)) \land (\forall s\in \operatorname{H}(e), \operatorname{norm}(\operatorname{K}(d, b, R, p, s)-1)\leq C\frac{1}{p^{2}})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/EvaluatedEulerCertificate.evaluated_certificate_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three index types J, I and T are finite and may be empty. The data d consist of integer linear coefficients a(j), correction multiindices n(i,j), signed integer powers c(i), tail multiindices u(t,j), and integer tail coefficients h(t). Write z^n for the product of z(j)^n(j) over J. Let U(z) be the product of (1-z^n(i))^max(c(i),0), V(z) the product of (1-z^n(i))^max(-c(i),0), and P(z) the sum of h(t) z^u(t). Certificate(d) means the identity (1+sum_j a(j)z(j)) U(z)=V(z)+P(z) for every complex vector z. These finite data and their identity precede all analytic choices.

In the formula, deg(n) is sum_j n(j), H(e) is the open halfplane Re(s)>e, and primes are natural primes. Set z(j)=exp(-b(j)s log(p)) and K(d,b,R,p,s)=(1+sum_j a(j)z(j)+R(p,s)) times the product of (1-z^n(i))^c(i), using integer powers. Analytic(f,H) denotes AnalyticOnNhd over the complex numbers: f is analytic at every point of H. Since H is open, this is the ordinary analytic-on-H condition.

The lower weight m is positive and satisfies m<=b(j) for every j. For a nonempty J it can be the minimum weight. Repeated and rationally dependent weights require no special cases. The order N may be zero, the cutoff inequality includes equality, and every positive e is allowed. The constant is chosen before R and is uniform in the prime and point.

For an explicit bound, put q=exp(-m e log(2)), B=product_i (1+q)^max(c(i),0), D=product_i (1-q)^max(-c(i),0), and L=sum_t |h(t)|. Then 0<q<1 and C=(L+A B)/D is valid. Each correcting monomial has norm at most q. Each tail monomial has norm at most p^(-2). The certificate gives K-1=(P+R U)/V, while the denominator norm is at least D>0. This proves the bound for the entire R family. Nonzero correcting binomials also justify analytic integer powers.

The remaining all-order problem is to construct, for every finite integer linear polynomial and N, such a certificate using only correction multiindices of degrees one through N and tails of degree at least N+1. This theorem assumes that finite algebraic identity; it does not construct the exponents. It asserts no nonvanishing of K, convergence of an infinite prime product, zero localization, or O-5 conclusion.

## References

- Truth anchor: `D5/S3/Analytic/EulerGerm/EvaluatedEulerCertificate.evaluated_certificate_uniform`
