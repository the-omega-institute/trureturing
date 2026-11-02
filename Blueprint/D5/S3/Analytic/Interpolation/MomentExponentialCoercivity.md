# Moment-sensitive exponential atomic-prefix coercivity

## Abstract

Actual primitive energy controls the exponentially weighted correlation of finite complex atomic prefixes, with an explicit moment-dependent coercivity constant.

**Theorem 1.1 (Exact quantitative bound for arbitrary complex atoms).**

Lean statement: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.moment_exponential_prefix_coercivity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.moment_exponential_prefix_coercivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real D>0, natural q>=1 and real lambda>0, for every finite index type I in any universe, every x:I to R in [0,D] and every a:I to C, suppose sum_i a(i)x(i)^r=0 for every natural r<=q. Put A(t)=AtomicPrefixEnergy.prefix(x,a,t), including atoms at t, and E=integral over R of norm(A)^2. Then 2 lambda (1-lambda^2 D^2/(4q(q+1))) E is at most the real part of sum_(i,j) conjugate(a(i)) a(j) exp(-lambda abs(x(i)-x(j))). All integrals are Bochner/Lebesgue integrals. The statement has no integrability premise. Empty families, repeated nodes, arbitrary complex phases, exact cancellation and E=0 remain in scope. The coefficient may be negative. Strict positivity requires both E>0 and lambda^2 D^2<4q(q+1).

Library reuse is literal: shifted_hinge_prefix_energy supplies square integrability of the actual prefix, exponential_prefix_energy supplies the exact complex identity Q_lambda=2 lambda E-lambda^2 T_lambda(A), and complex_L2_moment_primitive_gap supplies integral_[0,D] norm(B)^2<=D^2/(4q(q+1)) E for the actual B(t)=integral_0^t A. FiniteMomentCorrelation.finite_moment_correlation is inspected as the existing existential continuous-weight result; it is not renamed, copied or used as an explicit order estimate. Its polynomial approximation proof does not give this explicit q-constant.

The new inference is an exact finite causal energy calculation. Define B(t)=sum_i a(i) max(t-x(i),0), g(t)=sum_i a(i)(1-exp(-lambda max(t-x(i),0)))/lambda, h(t)=(B(t)-g(t))/lambda, and Z(t)=sum_(x(i)<=t) a(i) exp(-lambda(t-x(i))). Their right derivatives are B'=A, g'=Z=A-lambda g and h'=g at every real t, including coincident nodes. Continuity of B,g,h and the right-derivative form of FTC justify every integration. Prefix times continuous functions are integrable by a finite indicator expansion. The zeroth and first atomic moments give A(D)=B(D)=0; B(0)=g(0)=h(0)=0 follows from x(i)>=0. Right FTC identifies the explicit ramp B with the actual interval primitive on [0,D].

For any l,r in [0,D], integrate the overlap of the two causal exponentials from max(l,r) to D. The identity 2 max(l,r)-l-r=abs(l-r) yields 2 lambda integral_[0,D] z_l(t) z_r(t)+z_l(D) z_r(D)=exp(-lambda abs(l-r)). Finite complex summation therefore gives Re(Q_lambda)=2 lambda integral_[0,D] norm(Z)^2+norm(Z(D))^2. This pays the entire upper endpoint; it is also an explicit square representation rather than an assumed positive-definite kernel.

Let J=integral_[0,D] Re(conjugate(g) A), L=integral_[0,D] Re(conjugate(h) g), and E(f)=integral_[0,D] norm(f)^2. Right FTC for norm(g)^2 gives norm(g(D))^2=2J-2 lambda E(g), and right FTC for norm(h)^2 gives norm(h(D))^2=2L. The identities Z=A-lambda g and B=g+lambda h give E(Z)=E(A)-2 lambda J+lambda^2 E(g) and E(B)=E(g)+2 lambda L+lambda^2 E(h). Finally g(D)=-lambda h(D) and Z(D)=-lambda g(D). Substitution yields exactly Re(Q_lambda)=2 lambda E(A)-2 lambda^3 E(B)+2 lambda^5 E(h)+lambda^4 norm(h(D))^2. Both final terms are nonnegative for lambda>0. No infinite endpoint, Fourier transform, distributional differentiation, or unproved positivity supplier occurs.

The existing atomic exponential identity now converts the last calculation into Re(T_lambda(A))<=2 lambda E(B), on exactly its actual [-D,D] correlation window. This private bridge is consumed by the original endpoint. For each r<q, direct finite indicator integration gives integral_[0,D] t^r A(t)=[D^(r+1) sum_i a(i)-sum_i a(i)x(i)^(r+1)]/(r+1)=0. Thus atomic moments through q, a total of q+1 conditions, supply exactly q vanished prefix moments. Applying the merged primitive gap with that same q closes the displayed coefficient.

For the actual trivial-zero exponential series P(t)=sum_(k>=1) c_k exp(-lambda_k abs(t)), c_k=1/(2k(2k+1)) and lambda_k=2k+1/2, a finite head k<=K would contribute at least [sum_(k<=K) 2c_k lambda_k(1-lambda_k^2 D^2/(4q(q+1)))] E under the same atomic moments. Choose q before the atomic family. For example, lambda_K^2 D^2<=2q(q+1) gives each head term at least c_k lambda_k E. The existing exponential_prefix_coercivity supplies nonnegative energies for each remaining exponential term on the zero-mass subspace; transporting an infinite series still requires its actual convergence and interchange statements. This finite-head application is exposition, not a separate bind-only theorem.

The sufficient choice q comparable to lambda_K D is linear in D for fixed K. It does not establish N(D)=o(D). In the SublinearMomentGrowth convention r<m(D), these atomic conditions correspond to m(D)=q(D)+1. Actual transport of the full signed remainder R, its prime-power, smooth and ramp contributions, and a sufficient preselected sublinear order for full K=P+R positivity remain independent obligations. Nothing here concludes RH or actual-kernel positivity.

The companion Reg registration observes the literal complex real-part operation on the complete quadratic form. Its law retains the whole original telescope and all finite families; the rejected observation is constant -1, which fails already for an empty family at D=q=lambda=1. Dependence compares the real parts of 0 and 1. The mathematical construction is classical; no literature novelty or model-diverse review is claimed.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.moment_exponential_prefix_coercivity`
- Dependency: [D5/S3/Analytic/Interpolation/AtomicPrefixEnergy](AtomicPrefixEnergy.md)
- Dependency: [D5/S3/Analytic/MomentOrthogonalPrimitiveGap](../MomentOrthogonalPrimitiveGap.md)
