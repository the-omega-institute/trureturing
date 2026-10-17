# Archimedean Jump Decomposition

## Abstract

The completed-zeta Archimedean term is its mass contribution plus a nonnegative continuous translation energy.

**Theorem 1.1 (Actual jump density as a positive rate series).**

Lean statement: `D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition.jump_density_eq_tsum`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition.jump_density_eq_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x>0, archimedeanJumpDensity(x) equals the sum over natural n of exp(-((2*n)+1/2)*x). The geometric ratio exp(-2*x) lies in [0,1). This is the original density-series proof used by the Levy decomposition; the extended periodic comparison consumes the same declaration directly.

**Theorem 1.2 (Archimedean jump decomposition).**

$$\forall f\in \mathcal{W}, hArch: \operatorname{ArchimedeanConvergent}(\operatorname{convolutionSquare}\left(f\right)) \Rightarrow \operatorname{archimedeanTerm}\left(\operatorname{convolutionSquare}\left(f\right), hArch\right) = \operatorname{archimedeanConstant} \cdot \operatorname{l2Mass}\left(f\right) + \operatorname{archimedeanJumpEnergy}\left(f\right) \land 0 \le \operatorname{archimedeanJumpEnergy}\left(f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition.archimedean_jump_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The test function lies in the canonical carrier of even smooth compactly supported complex-valued functions. The displayed hArch premise is the exact integrability witness consumed by archimedeanTerm.

The jump density is exp(-x/2)/(1-exp(-2x)) on positive scales, and the jump energy integrates the squared displacement of f by translation against that density. The proof derives its Levy representation from the frozen digamma series and applies Fourier inversion and Tonelli.

The first public conjunct is the exact complex identity. The second public conjunct records positivity of the independently constructed continuous jump energy.

The same density has an exact interval L2 application. Let a>0, d=2*a, I=(-a,a], and u be complex-valued with MemLp(u,2,dx restricted to I). Write z=1_I*u for its zero extension and v for its d-periodic extension obtained from AddCircle.liftIoc at base point -a. For s>0, set rho(s)=exp(-s/2)/(1-exp(-2*s)), F0(s)=rho(s)*integral_R |z(x)-z(x-s)|^2 dx, and Fp(s)=rho(s)*integral_I |u(x)-v(x-s)|^2 dx. These use Lebesgue measure and the original half-open interval; no pointwise agreement of the two outer endpoints is assumed.

For epsilon>=0 define K_epsilon(x,y) as the sum over every nonzero integer m of rho(|x-y+m*d|) when epsilon<|x-y+m*d|, with that summand zero otherwise. Let B_epsilon be the real part of integral_{I x I} conjugate(u(x))*K_epsilon(x,y)*u(y) dx dy. This retains both nearest images and the whole remaining integer lattice, with the zero image omitted.

For each epsilon>0 both F0 and Fp are integrable on (epsilon,infinity), and their actual cutoff integrals satisfy E0_epsilon=Ep_epsilon+B_epsilon. The half-open periodic copies are disjoint and exhaustive. Their zero-image cancellation, Fubini and the full integer sum identify the difference of the two correlations with the image pairing. Reflection gives C(-s)=conjugate(C(s)); expanding both squared displacements gives precisely the displayed sign and coefficient of B_epsilon.

The boundary pairing at epsilon=0 is absolutely integrable under the interval L2 premise alone. For m=1 and m=-1, the possible corner singularities are bounded using the actual density and the Carleman integral estimate on the positive half-line. For |m|>=2, exponential decay gives a summable geometric majorant. Together these bounds dominate the entire image pairing in L1. Dominated convergence therefore gives B_{1/(n+1)} tending to B_0.

Consequently F0 is integrable on (0,infinity) if and only if Fp is integrable there. On this common finite domain the full energies obey E0=Ep+B_0. To obtain the forward direction, start with the finite full zero-extension energy, subtract the convergent boundary sequence from its cutoff integrals, and apply the nonnegative AECover integrability theorem to Fp. Starting with the finite periodic energy and adding the boundary sequence proves the converse. The sets (1/(n+1),infinity) cover (0,infinity), so each limit identifies the full integral only after its integrability has been established. No finiteness of either full energy is included in the original L2 premise.

The periodic energy also has an exact Fourier description on every such interval L2 input. Put omega_n=2*pi*n/d for n in Z, w(t)=Re(digamma(1/4+i*t/2))-Re(digamma(1/4)), and c_n=sqrt(d)*fourierCoeff(v,n). Mathlib's circle coefficient uses Haar measure of total mass one: equivalently, c_n is 1/sqrt(d) times the Lebesgue integral over I of u(x)*exp(-i*omega_n*x). Thus sum_n |c_n|^2 equals the original Lebesgue L2 mass; the factor sqrt(d) is essential.

With all terms interpreted in ENNReal, the full periodic energy is integral_{s>0} ofReal(rho(s))*ofReal(integral_I |u(x)-v(x-s)|^2 dx) ds =sum_{n in Z} ofReal(w(omega_n))*ofReal(|c_n|^2). This equality holds before imposing any full-energy finiteness premise and permits both sides to be infinite. The original Levy representation proves w(t)>=0 for every real t and identifies each frequency integral with this actual digamma increment.

For each fixed displacement s, L2 Parseval gives the squared mass of the periodic difference as the coefficient sum with multiplier |1-exp(-i*omega_n*s)|^2=2*(1-cos(omega_n*s)). Nonnegative Tonelli exchanges the sum with the s-integral. The already proved one-frequency Levy integrability and digamma identity then evaluate each weight. Only the finite L2 difference mass is converted from a real integral to its ENNReal integral; no infinite total energy is converted to a real number.

Combining this extended identity with the full boundary-domain equivalence yields the exact coefficient domain: F0 is integrable on (0,infinity) if and only if sum_{n in Z} ofReal(w(omega_n))*ofReal(|c_n|^2) is finite. The original premises remain a>0 and interval MemLp 2. On this common domain the finite identity E0=Ep+B_0 continues to hold.

These interval and Fourier conclusions apply the existing Gamma density and Levy proof together with the interval transport, Parseval and integration results. A closed form realization, a smooth compactly supported form core, identification with the full raw real-line Fourier multiplier on this domain, and positivity of the full signed Weil form require further arguments. The displayed public theorem above retains its smooth even test carrier and exact ArchimedeanConvergent premise.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition.archimedean_jump_decomposition`
- Truth anchor: `D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition.jump_density_eq_tsum`
- Dependency: [D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity](../TestFunctions/ConvolutionSquarePositivity.md)
