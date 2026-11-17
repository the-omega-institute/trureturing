# Signed Euler pole obstruction

## Abstract

The full complex Euler double-pole coefficient bounds every eventual signed tail envelope.

**Theorem 1.1 (Entire finite heads).**

Lean statement: `D5/S3/Analytic/Laplace/EulerPoleObstruction.finiteHead_entire`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/EulerPoleObstruction.finiteHead_entire` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let g be a real function integrable on the finite interval (U,V]. The function P(z)=integral over (U,V] of exp(-zu)g(u) is differentiable at every complex z, hence entire. No pointwise bound on g or global measurability assumption is required. The hypotheses are for the restricted Lebesgue measure.

On a compact complex neighborhood times the compact real interval, the derivative multiplier -u exp(-zu) has a uniform bound K. The integrable dominating function is K norm(g(u)). Differentiation under the integral therefore applies to arbitrary integrable sources, including unbounded ones. This is the usual dominated parameter integral argument; no originality is claimed.

**Theorem 1.2 (Positive half-plane analyticity).**

Lean statement: `D5/S3/Analytic/Laplace/EulerPoleObstruction.tail_analytic`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/EulerPoleObstruction.tail_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If g is integrable on (U,infinity) and U>=0, its actual Laplace integral is AnalyticOnNhd on Re z>0. At a given z, derivatives are dominated by exp(-1)/(Re z/2) times norm(g(u)), since u exp(-bu)<=exp(-1)/b for b>0. No convergence on a negative half-plane is asserted.

**Theorem 1.3 (Exact cutoff correction).**

Lean statement: `D5/S3/Analytic/Laplace/EulerPoleObstruction.tail_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/EulerPoleObstruction.tail_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For U>=0, V>=U, g integrable on (U,infinity), and Re z>0, the actual tail at V equals the actual tail at U minus finiteHead g U V z. The disjoint partition is (U,V] union (V,infinity)=(U,infinity). Both integrals converge absolutely on this positive half-plane.

**Theorem 1.4 (The positive-gap moment estimate).**

Lean statement: `D5/S3/Analytic/Laplace/EulerPoleObstruction.coefficient_le_of_pointwise_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/EulerPoleObstruction.coefficient_le_of_pointwise_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let g be real and integrable on (U,infinity), U>0, and d<sigma<0. Let Phi be meromorphic on Re z>d and analytic at every real x with sigma<=x<=0. Write L(z) for the actual integral of exp(-zu)g(u) over u>U and E(L)(z)=z L''(z)+2 L'(z). Assume E(L)=Phi only on Re z>0. At a nonreal point a with Re a=sigma assume the full complex punctured limit (z-a)^2 Phi(z) tends to a nonzero Lambda. For real s with s^2=1 and c>=0, the bound s g(u)<=c exp(sigma u)/u for every u>U implies norm(Lambda)<=norm(a)c.

The nonnegative gap c exp(sigma u)/u-s g(u) is an actual integrable density, giving a finite positive measure. Its comparison transform has explicit first and second derivatives. PositiveEulerContinuation.integrable_and_analytic_of_euler_corridor forces exponential integrability throughout Re z>sigma. The proof includes the finite-measure dominated convergence limit when its genuine convergence cut is zero and uses the full complex zero extension there.

At the real point sigma the signed solution extends across a disk by EulerLocalContinuation. The normalized first positive moment tends to zero and the normalized second moment tends to c. At a, the comparison Euler expression is analytic. Combining the original full complex pole limit with the Euler identity gives the signed coefficient on a rightward ray. Norm bounds for the actual positive moment integrals yield the entire coefficient estimate; neither moments nor negative-half-plane convergence are assumptions.

**Theorem 1.5 (An eventual envelope at the original cutoff).**

Lean statement: `D5/S3/Analytic/Laplace/EulerPoleObstruction.coefficient_le_of_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/EulerPoleObstruction.coefficient_le_of_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Keep exactly the same g,U,d,sigma,Phi,a,Lambda,s,c and the same hypotheses, but assume only eventually at real infinity that s g(u)<=c exp(sigma u)/u. The same conclusion norm(Lambda)<=norm(a)c follows. Choose V>U beyond the eventual bound. The removed finite head P is entire by finiteHead_entire, with domination proportional to norm(g), even when g is unbounded.

The later actual tail is L-P on Re z>0. Its forcing is Phi-E(P), meromorphic on the same half-plane and regular on the same real corridor. Subtracting the entire Euler expression preserves the full complex punctured coefficient Lambda, including its nonzero value. Apply the pointwise positive-gap estimate at V. This establishes the eventual statement for the original U and original Phi.

**Theorem 1.6 (Arbitrarily late peaks of both signs).**

Lean statement: `D5/S3/Analytic/Laplace/EulerPoleObstruction.signed_peaks`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/EulerPoleObstruction.signed_peaks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same actual integrability, positive cutoff, forcing equation, corridor regularity and full nonzero pole hypotheses, for every real s with s^2=1, every 0<=c<norm(Lambda)/norm(a), and every real T, some u>max(T,U) satisfies c<u exp(-sigma u)(s g(u)). If all such values were at most c, division by the positive normalization would give the forbidden eventual envelope.

Only forcing data at the original cutoff are needed: the finite-head correction supplies later cutoffs. In particular, an EulerTail family with actual g integrable at U0>0 and forcing, equation, real regularity and the same a,Lambda at every U>=U0 satisfies the complete all-cutoff conclusion by its data at U0. No additional family or signed-theta theorem is required.

The argument is a reusable form of the classical positive Laplace and local pole comparison method. It asserts no zeta zero, RH truth value, arithmetic error rate, effective peak location, or endpoint coefficient equality, and makes no literature originality claim.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/EulerPoleObstruction.coefficient_le_of_envelope`
- Truth anchor: `D5/S3/Analytic/Laplace/EulerPoleObstruction.coefficient_le_of_pointwise_envelope`
- Truth anchor: `D5/S3/Analytic/Laplace/EulerPoleObstruction.finiteHead_entire`
- Truth anchor: `D5/S3/Analytic/Laplace/EulerPoleObstruction.signed_peaks`
- Truth anchor: `D5/S3/Analytic/Laplace/EulerPoleObstruction.tail_analytic`
- Truth anchor: `D5/S3/Analytic/Laplace/EulerPoleObstruction.tail_cutoff`
- Dependency: [D5/S3/Analytic/Laplace/PositiveEulerContinuation](PositiveEulerContinuation.md)
