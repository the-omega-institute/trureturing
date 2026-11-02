# Full actual-kernel finite-codimension coercivity and strictness

## Abstract

The complete actual arithmetic kernel has any prescribed prefix-energy coercivity, with genuine grouped-measure strictness, on a uniformly selected finite-codimension ordinary-moment subspace of each fixed positive window.

This is the compiled result for the active RH research problem. The D5 source and its imported bridges compile on the pinned Lean and Mathlib toolchain, with standard3 closure. The same-unit Reg source compiles and records the complete telescope, while its dependent-family source binding remains declared_unresolved under the linked audit issue. The existing source clause is AURIC_PRIME_POWER_DIFFERENCE_COUPLING_FINITE_CODIMENSION_POSITIVITY_AND_ROOT_ROBIN_BUDGET, Section 5, Theorem 2, equations (17)-(20), and Appendix C. Eventual canonical integration must ingest and deposit or cover this existing clause; deposit-uncovered is not the route for this content.

**Theorem 1.1 (One moment order before every finite atomic family).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelFiniteCodimension.actual_kernel_finite_codimension_coercivity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelFiniteCodimension.actual_kernel_finite_codimension_coercivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real D>0 and real kappa>0, there exists a natural N>=1 such that, for every finite index type I in an arbitrary universe, every real function x:I to R and every complex function a:I to C, if all nodes satisfy 0<=x(i)<=D and sum_i a(i) x(i)^r=0 for each natural r<=N, then kappa times the integral over R of norm(F(v)) squared is at most the real part of sum_i,j conjugate(a(i)) a(j) K(x(i)-x(j)); moreover, if some grouped node mass sum_{i:x(i)=t} a(i) is nonzero, that real part is strictly positive. Here F(v)=sum_i (if x(i)<=v then a(i) else 0) includes the endpoint, and all integrals use Lebesgue measure. The existential N precedes I, its Fintype instance, both whole functions and their hypotheses. Empty families, repeated nodes, arbitrary orderings, coefficient cancellation and E=0 are included. The strict clause concerns the actual coalesced finite atomic measure, not a nonzero coefficient vector. No atom-count bound, separation premise, small-window hypothesis, assumed curvature bound or dependence of N on the atoms appears.

The kernel is literally ActualKernelLocalPositivity.K(t)=exp(-abs(t)/2) times (U(exp(abs(t)))-log(2 pi)+trivialT(abs(t))). The complete trivial-zero term is P(t)=exp(-abs(t)/2) trivialT(abs(t)), with trivialT(y)=sum_n c(n) exp(-2(n+1)y), c(n)=1/(2(n+1)(2(n+1)+1)). Thus lambda(n)=2(n+1)+1/2 and P(t)=sum_n c(n) exp(-lambda(n) abs(t)). All n>=0 occur, including at t=0. The proof does not substitute ActualKernelCusp.R or another generic kernel for K-P.

First prove abs(c(n) exp(-lambda(n) abs(t)))<=c(n), since lambda(n)>0 and exp(-lambda(n) abs(t))<=1. The exact coefficient HasSum from TrivialZeroLaplace gives summability; factoring the damping exponential through the tsum identifies the sum with the literal complete P. For each pair i,j the complex quadratic summand is absolutely dominated by norm(conjugate(a(i)) a(j)) c(n). Norm summability gives a HasSum for that pair, and two finite HasSum sums give Q_P=sum_n c(n) Q_lambda(n). This is an absolutely convergent series of the original quadratics. No weighted-rate infinite series is exchanged with an integral or with the energy.

For zero total mass, the existing exponential_prefix_coercivity gives Re(Q_lambda)>=2 lambda exp(-lambda D) E>=0, where E=integral norm(F) squared>=0. Taking real parts of the proved complete quadratic HasSum, each weighted summand is nonnegative. The Mathlib sum_le_hasSum inequality therefore makes the complete Q_P dominate every finite prefix. The tail is controlled by its own nonnegative original quadratic terms; it is never replaced by a divergent sum of multiples of E.

For each n, direct fraction algebra gives c(n) lambda(n)-1/(4(n+1))=1/(2(2(n+1)+1))>=0. Mathlib Real.tendsto_sum_range_one_div_nat_succ_atTop then supplies a finite J with sum_{n<J} c(n) lambda(n)>=kappa+M. This proves the needed harmonic growth from the actual coefficients. There is no assertion that sum_n c(n) lambda(n) is finite or summable.

For any lambda>0, apply finite_moment_correlation to w(s)=exp(-lambda abs(s)) on [-D,D] with tolerance 1/lambda. Its order is selected before the atom type and all atom data. The exact exponential_prefix_energy identity is Q_lambda=2 lambda E-lambda squared W, with W=integral_{[-D,D]} exp(-lambda abs(s)) C(s) and C(s)=integral conjugate(F(v+s)) F(v). Since Re(W)<=norm(W)<=E/lambda, the identity yields Re(Q_lambda)>=lambda E. It never divides by E. Apply this to the finitely many lambda(n), n<J; choose their orders and take N=max(1,max_{n<J} order(n)), then use the inclusive hypotheses r<=N (only the needed subrange r<order(n) is consumed). The empty prefix J=0 is handled by the finite supremum convention and the explicit maximum with one.

The existing actual_remainder_prefix_bound chooses a finite M>=0 using only D before all finite atom data, and gives norm(Q_(K-P))<=M E under zero mass. The zeroth inclusive moment gives zero mass because N>=1. The finite prefix and improved exponential bounds give Re(Q_P)>=(kappa+M) E. The norm bound gives Re(Q_(K-P))>=-M E. The exact finite-sum identity Q_K=Q_P+Q_(K-P) then gives Re(Q_K)>=kappa E. For strictness, collect the finite distinct node values T and grouped masses b(t)=sum_{i:x(i)=t}a(i), choose the least y with b(y) nonzero, and take a positive gap with no later node. Earlier grouped masses vanish, so F is b(y) on a right interval of positive length; the last endpoint cannot carry a nonzero grouped mass because total mass is zero. Thus E>0, and kappa>0 gives Re(Q_K)>0. The remainder bound is consumed through the existing public theorem, with no copied or replacement proof.

Only this public theorem is proposed. All helpers, including the grouped-mass energy witness, full series interchange, nonnegative tail argument, harmonic prefix construction and simultaneous moment selection, are private and consumed by its live proof. The proposed substantive content is this complete coefficient-series, arithmetic join and genuine strictness clause; proof-shape and admission remain unassessed until canonical elaboration and dependency review. No separate named bind-only application theorem is added.

The same-unit Reg owner attempts the complete telescope with the final Complex.re observation at both result conjuncts. The actual realization is real part; the constant-minus-one intervention violates the coercivity conjunct on an empty family for every candidate N. Actual observation depends on its complex input, as witnessed by zero and one. The existing dependent-family template supplies whole-family sensitivity. The sourceSelection paths are recorded as proposals, and the current audit is declared_unresolved with the linked issue for source binding classification.

This source addresses fixed-window finite-codimension coercivity and genuine grouped-measure strictness only. It assumes and concludes no RH statement, proves no all-direction PSD assertion, and claims no sublinear moment-order growth with D. The exact theorem and same-unit Reg source compile; independent audit, freeze and merge remain outside this source.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelFiniteCodimension.actual_kernel_finite_codimension_coercivity`
- Dependency: [D5/S3/Analytic/Interpolation/FiniteMomentCorrelation](../../../Analytic/Interpolation/FiniteMomentCorrelation.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelPrefixPerturbation](ActualKernelPrefixPerturbation.md)
