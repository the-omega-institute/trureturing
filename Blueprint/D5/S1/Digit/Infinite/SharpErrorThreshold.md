# Sharp closed and open error thresholds

## Abstract

Sharp closed and open error thresholds.

**Theorem 1.1 (Sharp closed and open error thresholds).**

Lean statement: `D5/S1/Digit/Infinite/SharpErrorThreshold.result`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SharpErrorThreshold.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A source is any infinite Boolean stream with no adjacent occupied bits. For either incoming guard and every h>=1, its first h three-bit windows are recovered from h+1 consecutive real samples. Put t=1/phi and a=t^3. The source class for guard zero is the complete class; guard one requires the first bit to be empty. Correctness means that every source compatible with the same observation has the returned prefix.

For each nonnegative radius epsilon, uniform recovery under the closed supremum-error contract exists exactly when epsilon<t/4. Under the positive-radius open contract it exists exactly when 0<epsilon<=t/4. Both conclusions hold for either guard.

The decoder chooses, independently at every window j, the translation nearest to the observed residual d_j=r_j+a*r_(j+1). The actual residual identity and 1+a=2t give |d_j-Delta_(sigma_j)|<=2t*epsilon for closed errors and a strict inequality for open errors. Distinct translations differ by at least t^2, so residual error strictly below t^2/2 gives a unique nearest translation equal to the actual window.

Below the closed threshold, the uniform decision margin is m=t^2/2-2t*epsilon=2t*(t/4-epsilon)>0. For every other translation, the residual is at least m away from the midpoint decision boundary. At the open critical radius, each residual still has its own positive margin t^2/2-|d_j-Delta_(sigma_j)|; no uniform positive margin for all critical observations is asserted.

The constant observation t/4 is at distance t/4 from both the empty source response and the periodic five response. Their prefixes differ for h>=1, and both sources obey either guard. This excludes closed recovery at and above t/4 and open recovery strictly above t/4.

Finite precision is stable below the strict threshold: if rho>0 and epsilon+rho<t/4, rational sample vectors within rho of an observation exist. Every such vector has total source error at most epsilon+rho, its residual error is at most 2t*(epsilon+rho)<t^2/2, and the same nearest-translation decoder returns the actual prefix. These rational residuals and the five translations lie in Q(t), where exact arithmetic can implement the finite set of comparisons.

## References

- Truth anchor: `D5/S1/Digit/Infinite/SharpErrorThreshold.result`
- Dependency: [D5/S1/Digit/Infinite/CriticalPrefixSeparation](CriticalPrefixSeparation.md)
