# Actual arithmetic remainder and atomic prefix energy

## Abstract

The complete actual arithmetic remainder has a uniform finite atomic prefix-energy cost on every fixed window.

**Definition 1.1 (Explicit finite component-curvature cost).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelPrefixPerturbation.finite_curvature_cost`

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelPrefixPerturbation.finite_curvature_cost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real D and natural N, finite_curvature_cost(D,N) is cost(B',B'',0,D) plus the sum over n<N with 2<=n and log(n)<=D of cost(g_n',g_n'',log(n),D), where cost(f1,f2,ell,D)=2(abs(f1(ell))+the Lebesgue integral over Icc(ell,D) of abs(f2(s))). The functions B and g_n and their derivatives are given below. This is a finite sum of component costs. Cancellations can make the total variation of the combined distributional second derivative smaller.

**Theorem 1.2 (Constructive bound with the exact finite cost).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelPrefixPerturbation.actual_remainder_prefix_bound_with_finite_cost`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelPrefixPerturbation.actual_remainder_prefix_bound_with_finite_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real D>0 and every natural N with exp(D)<N, finite_curvature_cost(D,N)>=0 and, for every universe-polymorphic finite I, x:I to R in [0,D] and a:I to C with sum_i a(i)=0, the norm of sum_i sum_j conjugate(a(i))a(j)(K(x(i)-x(j))-exp(-abs(x(i)-x(j))/2)trivialT(abs(x(i)-x(j)))) is bounded by finite_curvature_cost(D,N) times integral_R norm(prefix(x,a,v))^2 dv. D and N precede all atomic data; the literal complete K-P and endpoint-inclusive prefix are retained. No further moments, positivity, RH, node-dependent constant or division by the energy is used.

Finite arithmetic localization, the exact Volterra identities and the shifted-hinge estimate prove this constructive bound. The original existential theorem chooses N by the Archimedean property and directly uses this bound. The explicit cost is the finite-window intermediate in Appendix H of the owning theory. The total-variation formulation of equation (19), Fourier Appendix C and finite-codimension coercivity remain separate mathematical questions.

**Theorem 1.3 (Uniform actual remainder bound).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelPrefixPerturbation.actual_remainder_prefix_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelPrefixPerturbation.actual_remainder_prefix_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real D>0 there exists a real M>=0 such that, for every finite index type I in every universe, every x:I to R with x(i) in [0,D], and every a:I to C with sum_i a(i)=0, the norm of sum_i sum_j conjugate(a(i)) a(j) R(x(i)-x(j)) is at most M times the Lebesgue integral over the real line of norm(prefix(x,a,v)) squared. Here K is literally ActualKernelLocalPositivity.K, P(t)=exp(-abs(t)/2) trivialT(abs(t)) is the complete trivial-zero kernel, and R=K-P. M is chosen before I,x,a. The prefix is the published right-continuous endpoint-inclusive finite sum. Empty types, arbitrary cardinality, repeated/coincident/overlapping atoms, zero coefficients and jumps at both endpoints are included. No distinctness, separation, coefficient bound, nonemptiness, moment condition beyond mass zero, RH or PNT is assumed.

Choose a natural N with exp(D)<N and S={n<N: 2<=n and log(n)<=D}. Exact finite-on-compact localization uses the existing mangoldtPart_eq_range; this shared identity is applied to the complete actual ramp sum. Both Lambda(0) and Lambda(1) are treated as zero before any division or threshold argument. Put B(r)=exp(r/2)(1+gamma-r)-log(2pi)exp(-r/2), g_n(r)=Lambda(n)(exp(r/2)/n-exp(-r/2)), and ell_n=log(n). On abs(t)<=D the literal R(t) equals B(abs(t)) plus the sum over n in S of g_n(abs(t)) when ell_n<=abs(t), and zero otherwise. This localization asserts no global truncation of the actual arithmetic sum.

The private derivative formulas are B'(r)=exp(r/2)((1+gamma-r)/2-1)+log(2pi)exp(-r/2)/2, B''(r)=B(r)/4-exp(r/2), g_n'(r)=Lambda(n)(exp(r/2)/n+exp(-r/2))/2, and g_n''(r)=g_n(r)/4. In particular B'(0)=(gamma-1+log(2pi))/2. Each g_n(ell_n)=0. The actual slope g_n'(ell_n) is retained as its exact elementary expression in the constant; this pays each derivative jump without needing a square-root normalization in the implementation.

For smooth f with f(ell)=0, integrating the explicit primitive (r-s)f'(s)+f(s) proves the exact Taylor/Volterra identity. Truncation at r=abs(t), including r=ell and r=D, gives clipped(f)(t)=f'(ell) max(abs(t)-ell,0)+integral_[ell,D] max(abs(t)-s,0) f''(s) ds. All scalar and complex finite-window integrands are continuous on compact intervals, so their integrability and the finite sum/integral exchanges are justified. This identity is proved from the actual smooth functions, not postulated as a representation hypothesis in the public theorem.

For s>=0, the absolute shifted hinge is the sum of the two oriented hinges. Swapping i,j shows the second quadratic is the conjugate of the first. The published shifted_hinge_prefix_energy bounds each norm by E=integral_R norm(prefix)^2, hence the absolute hinge form has norm at most 2E. This is an absolute bound; it asserts no sign for shifted correlations or their real parts. Constant kernels cancel by zero total mass. Multiplying the exact Volterra identities by conjugate(a(i))a(j), exchanging finite sums and compact integrals, and integrating the absolute-value bound yields the result.

A finite witness used by the proof is M=2(abs(B'(0))+integral_[0,D] abs(B''(s)) ds)+sum_{n in S} 2(abs(g_n'(ell_n))+integral_[ell_n,D] abs(g_n''(s)) ds). Every integral is a genuine compact integral of a continuous function; S depends only on D and the chosen N, and every summand is nonnegative. The origin slope and every active arithmetic corner, including entry at D, are paid. The proof uses no coefficient-norm or cardinality-dependent estimate.

This is the finite perturbation estimate for the complete actual kernel. It proves no global PSD, no full actual-K finite-codimension positivity and no RH claim by itself. Finite-codimension coercivity additionally requires a uniform high-moment correlation estimate and growth of the complete positive-kernel mixture.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelPrefixPerturbation.actual_remainder_prefix_bound`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelPrefixPerturbation.actual_remainder_prefix_bound_with_finite_cost`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelPrefixPerturbation.finite_curvature_cost`
- Dependency: [D5/S3/Analytic/Interpolation/AtomicPrefixEnergy](../../../Analytic/Interpolation/AtomicPrefixEnergy.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity](ActualKernelLocalPositivity.md)
