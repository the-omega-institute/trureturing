# A finite bootstrap of the actual zero strip

## Abstract

Strip improvement from weighted negative mass on Robin windows

Fix a real outer exponent b>1 and use the actual prime-power kernel k(t)=(ψ(t)-t)/t². Write E(B) for its terminal defect and M(Y,B) for its weighted negative mass. A seed of width α>0 means that every actual nontrivial zero ρ has Re(ρ)≤1-α.

**Theorem 1.1 (Decay of the scaled endpoint payment).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ZeroFreeStripRobinWindow.tendsto_sqrt_mul_negative_endpoint_of_actual_strip`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ZeroFreeStripRobinWindow.tendsto_sqrt_mul_negative_endpoint_of_actual_strip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the seed has 0<α≤1/2 and αb≥1/2, then sqrt(Y) max(-E(Y^b),0) tends to zero as real Y tends to infinity. The terminal-defect estimate bounds it by C Y^(1/2-αb)/(b log Y) for Y≥exp(1). At αb=1/2 the logarithmic denominator supplies the decay.

**Theorem 1.2 (Improving the actual strip).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ZeroFreeStripRobinWindow.actual_strip_improvement_of_frequently_small_weighted_negative_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ZeroFreeStripRobinWindow.actual_strip_improvement_of_frequently_small_weighted_negative_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume an actual seed strip of width 0<α≤1/2 and that for each real η>0 there are arbitrarily large real Y with M(Y,Y^b)≤Y^η. Then every actual nontrivial zero has real part at most 1-min(1/2,bα). For a zero violating this bound, set p=max(0,1/2-bα) and choose p<η<q<Re(ρ)-1/2. On a common late window the interior mass and endpoint payment sum to at most (1+C)Y^η<Y^q. The Robin budget lower bound from the zero gives at least Y^q on every sufficiently late window.

**Theorem 1.3 (Finite iteration to the critical line).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ZeroFreeStripRobinWindow.rh_of_frequently_small_weighted_negative_mass_of_actual_strip`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ZeroFreeStripRobinWindow.rh_of_frequently_small_weighted_negative_mass_of_actual_strip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start with any positive seed width α and the same arbitrarily late mass bound for every η>0 at one fixed b>1. Put α₀=min(1/2,α). After n iterations the strip width is min(1/2,b^n α₀). Since b>1 and α₀>0, a finite n reaches 1/2. The right-half-strip reduction then yields the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/ZeroFreeStripRobinWindow.actual_strip_improvement_of_frequently_small_weighted_negative_mass`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/ZeroFreeStripRobinWindow.rh_of_frequently_small_weighted_negative_mass_of_actual_strip`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/ZeroFreeStripRobinWindow.tendsto_sqrt_mul_negative_endpoint_of_actual_strip`
- Dependency: [D5/S3/Arith/Robin/Analytic/ZeroFreeStripMertensEnvelope](ZeroFreeStripMertensEnvelope.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RobinWindowMass](../../../Weil/Mertens/IntegratedExplicit/RobinWindowMass.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../../../Weil/ZetaBridge/RightHalfStripRiemannReduction.md)
