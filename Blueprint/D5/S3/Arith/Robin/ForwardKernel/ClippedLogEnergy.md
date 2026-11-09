# Translation energy of clipped logarithms

## Abstract

A clipped logarithmic cusp has translation energy bounded linearly in the step, uniformly in its inner and outer radii.

**Theorem 1.1 (Clipping in logarithmic coordinates).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy.clippedLog_log_space`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy.clippedLog_log_space` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<h<k and y nonzero, the clipped logarithm equals min(log(k),max(log(h),log(abs(y))))-log(k).

For 0<h<k, write ell(y)=log(min(k,max(h,abs(y)))/k). The unit logarithmic jump is J(z)=log(abs(z+1))-log(abs(z)). All integrals on the real line use Lebesgue measure.

**Theorem 1.2 (Local square integrability of the logarithm).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy.intervalIntegrable_log_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy.intervalIntegrable_log_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real endpoints a and b, log(x)^2 is interval integrable from a to b. For positive x, the shared bound log(x)^2<=16*x^(-1/2)+x^2 supplies an integrable majorant on every bounded positive interval; reflection handles negative arguments.

**Theorem 1.3 (Continuity of the clipped cusp).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy.clippedLog_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy.clippedLog_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<h<k, ell is continuous on the whole real line. The positive inner radius keeps the argument of the logarithm away from zero.

**Theorem 1.4 (Finite energy of the unit logarithmic jump).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy.logJump_sq_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy.logJump_sq_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The function J(z)^2 is integrable over the whole real line. Local square integrability of the logarithm controls the singularities at zero and minus one. For abs(z)>=2, abs(J(z))<=2/abs(z), so its square is dominated by an integrable inverse-square tail.

**Theorem 1.5 (Uniform linear translation-energy bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy.clippedLog_translation_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy.clippedLog_translation_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is an absolute constant C>0 such that, for every 0<h<k and u>0, the squared difference (ell(y+u)-ell(y))^2 is integrable over the real line and its integral is at most C*u.

Clipping between log(h) and log(k) is a map with Lipschitz constant one. Away from the two points zero and -u, the clipped difference is therefore bounded in absolute value by abs(log(abs(y+u))-log(abs(y))). The substitution y=u*z identifies the square of this latter difference with J(z)^2 and multiplies its integral by u. One can take C=1+integral(J(z)^2). This estimate controls the variance contribution of each translated cusp without a dependence on its depth log(k/h).

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy.clippedLog_continuous`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy.clippedLog_log_space`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy.clippedLog_translation_energy`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy.intervalIntegrable_log_sq`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy.logJump_sq_integrable`
- Dependency: [D5/S3/Analytic/LogSquareBound](../../../Analytic/LogSquareBound.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs](CommonBandSharpnessDefs.md)
