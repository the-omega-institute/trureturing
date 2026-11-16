# Finite integer Euler cancellation

## Abstract

Every finite integer linear polynomial has signed Euler cancellation to any total degree.

**Theorem 1.1 (Algebraic construction and uniform analytic evaluation).**

$$\begin{aligned}\forall J:\operatorname{Type}(),[\operatorname{Fintype}(J)], \forall a:J\Rightarrow\mathbb{Z}, \forall N\in \mathbb{N},\\\exists c:\operatorname{E}(J, N)\Rightarrow\mathbb{Z},\\(\forall u:J\Rightarrow\mathbb{N}, \operatorname{deg}(u)\leq N \implies \operatorname{L}(a, N, c, u)=0) \land\\\operatorname{Certificate}(\operatorname{D}(a, N, c)) \land\\(\forall i\in \operatorname{E}(J, N), 1\leq \operatorname{deg}(\operatorname{mode}(\operatorname{D}(a, N, c), i)) \land\operatorname{deg}(\operatorname{mode}(\operatorname{D}(a, N, c), i))\leq N) \land\\(\forall t\in \operatorname{support}(\operatorname{Hpoly}(a, N, c)), N+1\leq \operatorname{deg}(\operatorname{tailMode}(\operatorname{D}(a, N, c), t))) \land\\\forall b:J\Rightarrow\mathbb{R}, \forall m,e,A\in \mathbb{R},\\0<m \land (\forall j\in J, m\leq \operatorname{b}(j)) \land 0<e \land 0\leq A \land 2\leq (N+1)em \implies\\\exists C\in \mathbb{R}, 0\leq C \land \forall R:\operatorname{Primes}()\Rightarrow\mathbb{C}\Rightarrow\mathbb{C},\\(\forall p\in \operatorname{Primes}(), \operatorname{Analytic}(\operatorname{R}(p), \operatorname{H}(e))) \land (\forall p\in \operatorname{Primes}(), \forall s\in \operatorname{H}(e), \operatorname{norm}(\operatorname{R}(p, s))\leq A\frac{1}{p^{2}}) \implies\\\forall p\in \operatorname{Primes}(), \operatorname{Analytic}(\operatorname{K}(\operatorname{D}(a, N, c), b, R, p), \operatorname{H}(e)) \land (\forall s\in \operatorname{H}(e), \operatorname{norm}(\operatorname{K}(\operatorname{D}(a, N, c), b, R, p, s)-1)\leq C\frac{1}{p^{2}})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/FiniteIntegerEulerCancellation.finite_integer_euler_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite type J and N>=0, E(J,N) consists of all functions u:J->N with 1<=deg(u)<=N, where deg(u)=sum_j u(j). The coefficients a:J->Z have arbitrary signs. Write Q=1+sum_j a(j)X(j), U=product_u (1-X^u)^max(c(u),0), V=product_u (1-X^u)^max(-c(u),0), and Hpoly(a,N,c)=Q*U-V. All polynomial powers are natural powers. In the formula D(a,N,c) is the finite data with linear coefficients a, correction modes u in E(J,N), powers c(u), tail indices support(Hpoly(a,N,c)), tail modes t and tail coefficients coeff(Hpoly(a,N,c),t). L(a,N,c,u) is coeff(Hpoly(a,N,c),u).

The construction uses the variable ideal I in Z[X(j)]. Its d-th power consists exactly of polynomials whose coefficients below degree d vanish. Suppose Hpoly=QU-V belongs to I^d and V has constant coefficient one. Let r(u)=coeff(Hpoly,u) for each degree-d mode in support(Hpoly). Multiply U by A=product_u(1-X^u)^max(r(u),0), and V by B=product_u(1-X^u)^max(-r(u),0). In the quotient by I^(d+1), the degree-d monomials have pairwise zero products since d>=1. Polynomial.eval_add_of_sq_eq_zero applied to p=X^k, x=1 and y=-x gives (1-x)^k=1-k*x whenever x*x=0, including k=0. Thus A-B=-sum_u r(u)X^u in this quotient. The exact identity QUA-VB=Hpoly*A+V(A-B) removes the complete degree-d homogeneous component. The new error belongs to I^(d+1). Different degrees have disjoint modes.

Starting with U=V=1 and Q-1 in I, finite induction constructs the exponents through degree N. Unused modes are filled with zero. The finite-support and ordinary-function index presentations are transported by Finsupp.equivFunOnFinite and preserve total degree. Every actual tail index has degree at least N+1, since its coefficient is nonzero. Expanding the finite polynomial support and applying eval2 gives Certificate(D) for every complex vector, including zeros of correcting binomials. No division is used in this identity.

Certificate(D) means (1+sum_j a(j)z(j))U(z)=V(z)+P(z) for all complex z, where P is the finite tail sum. Let H(e)={s:Re(s)>e}, z(j)=exp(-b(j)s log(p)), and K(D,b,R,p,s) be (1+sum_j a(j)z(j)+R(p,s)) product_u(1-z^u)^c(u), using integer powers. Analytic(f,H) means AnalyticOnNhd over C. The existing evaluated_certificate_uniform theorem applied to the constructed D gives the displayed analytic conclusion. The exponent choice precedes b,m,e,A and the entire family R; C precedes R. Repeated and dependent weights are allowed and equality is allowed in the cutoff.

The result also allows empty J. At N=0 the correction set is empty and Hpoly=Q-1; Hpoly need not be zero. For Q=1+X and N=1, c(X)=1 gives Hpoly=-X^2. This is a finite algebraic consequence of classical integer Euler extraction, rather than a claim of new mathematics. Delabarre, Extension of Estermann's theorem to Euler products associated to a multivariate polynomial, BSMF 141 (2013), 225-265, DOI 10.24033/bsmf.2647, section 1.1 and section 2.2, Lemma 2, equations (5)-(6), Remark 4, printed pages 233-235, gives an integral expansion Q=product(1-Y^u)^gamma(u), with c=-gamma. For S=sum_j |a(j)|>0, this infinite product converges absolutely when every |Y(j)|<1/S; the case S=0 is trivial since Q=1. The finite cleared polynomial identity holds for every complex vector. The finite cleared polynomial assertion is proved here; it is not the literal statement of that paper. The primary source is https://www.numdam.org/item/BSMF_2013__141_2_225_0.pdf. No infinite prime product, nonvanishing, zero localization, or O-5 conclusion is asserted.

## References

- Truth anchor: `D5/S3/Analytic/EulerGerm/FiniteIntegerEulerCancellation.finite_integer_euler_cancellation`
- Dependency: [D5/S3/Analytic/EulerGerm/EvaluatedEulerCertificate](EvaluatedEulerCertificate.md)
