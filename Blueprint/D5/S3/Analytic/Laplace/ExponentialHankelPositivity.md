# Exponential Hankel positivity on an open half-line

## Abstract

Polynomial squares in the exponential coordinate detect positivity of an actual continuous signed L1 density.

**Definition 1.1 (Actual exponential moments).**

Lean statement: `D5/S3/Analytic/Laplace/ExponentialHankelPositivity.exponentialHankel`

*Formalization.* `D5/S3/Analytic/Laplace/ExponentialHankelPositivity.exponentialHankel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real cutoff U and a real density g, put h(k) = integral over u>U of g(u) exp(-k(u-U)) du, with k a natural number including zero. The matrix H(U,g,N) has rows and columns indexed by Fin(N+1), and entry h(i+j). Its entries are integrals of the supplied signed source.

**Theorem 1.2 (All depths detect pointwise positivity).**

$$\forall U \in \mathbb{R}, \forall g \in \mathbb{R} \to \mathbb{R}, (\operatorname{ContinuousOn}(g, \operatorname{Ioi}(U)) \land \operatorname{IntegrableOn}(g, \operatorname{Ioi}(U))) \Rightarrow (\forall k \in \mathbb{N}, \operatorname{IntegrableOn}(\operatorname{w}(U, g, k), \operatorname{Ioi}(U))) \land (\forall N \in \mathbb{N}, \forall c \in \operatorname{Coeff}(N), \operatorname{IntegrableOn}(\operatorname{v}(U, g, N, c), \operatorname{Ioi}(U)) \land \operatorname{Q}(\operatorname{H}(U, g, N), c) = \operatorname{Integral}(\operatorname{v}(U, g, N, c), \operatorname{Ioi}(U))) \land ((\forall u \in \operatorname{Ioi}(U), 0 \leq \operatorname{g}(u)) \Leftrightarrow (\forall N \in \mathbb{N}, \operatorname{PosSemidef}(\operatorname{H}(U, g, N))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/ExponentialHankelPositivity.exponential_hankel_positivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real U and g:Real->Real continuous and integrable on (U,infinity), every moment integrand is integrable. For every natural N and every real coefficient vector c:Fin(N+1)->Real, let p(c,t) = sum over i of c(i)t^i. The function v(U,g,N,c)(u) = g(u)p(c,exp(-(u-U)))^2 is integrable and c^T H(U,g,N)c equals its integral. In the formula, w(U,g,k)(u) denotes g(u)exp(-k(u-U)), Q is this actual matrix quadratic form, and Integral integrates on (U,infinity) with Lebesgue measure. Coeff(N) denotes the entire real space Fin(N+1)->Real.

The density is pointwise nonnegative throughout the open half-line if and only if H(U,g,N) is positive semidefinite for every natural N. No value or continuity is required at U or at infinity. L1 alone controls the bounded exponential weights and every polynomial square.

For the converse, a negative interior value gives a neighborhood in the coordinate t=exp(-(u-U)) where the density is negative. A continuous triangular hat centered there vanishes outside that neighborhood. Weierstrass approximation on [0,1] and dominated convergence extend polynomial-square positivity to the hat square. Its weighted integral is nonpositive, hence zero; continuity on the open half-line then contradicts its nonzero value at the chosen point. Only the hat is approximated on the closed interval. The density need not extend to either compactification endpoint. This is a classical polynomial-density positivity mechanism; no priority claim is made.

For an exponential upper cap, fix b>0 and a continuous integrable f on (U,infinity), and set g(u)=C exp(-bu)-f(u). The exponential term is integrable. Its kth moment is C exp(-bU)/(b+k), so the Hankel entry is C exp(-bU)/(b+i+j) minus the corresponding exponential moment of f. For each fixed C>=0, the theorem equates positivity of all these matrices with f(u)<=C exp(-bu) for every u>U. Consequently an existential cap must have order exists C>=0, forall N. The SAME C must work at every depth. The order forall N, exists C does not supply a common cap; this theorem does not assert fixed-depth cap feasibility or an effective witness depth.

The analytic equivalence establishes no cap existence and makes no assertion about zeta zeros. A zero-exclusion application additionally needs an independently established actual-tail supplier. A supplier valid for 0<b<1/2 gives only its corresponding strip Re(rho)>1-b; it supplies neither the b=1/2 endpoint nor an RH converse.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/ExponentialHankelPositivity.exponentialHankel`
- Truth anchor: `D5/S3/Analytic/Laplace/ExponentialHankelPositivity.exponential_hankel_positivity`
