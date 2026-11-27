# The entropy minimizer and coefficient

## Abstract

Rational logarithm estimates enclose the unique minimizer and its negative profile value.

Let I(t) be the integral over 0<=u<=1 of -h(tu), where h is the binary entropy with natural logarithms. The profile has a unique minimum on the closed unit interval. Its negative is the coefficient kappa.

**Theorem 1.1 (Certified intervals).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/EntropyMinimum.entropy_minimum_enclosure`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Compression/EntropyMinimum.entropy_minimum_enclosure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real minimizer t in [0,1], meaning that I(t)<=I(v) for every v in [0,1], the theorem proves 0.76075660<=t<=0.76075661 and 0.55020623<-I(t)<0.55020624. Every decimal endpoint is an exact rational number. Existence and uniqueness of this minimizer come from the entropy profile theorem.

The logarithm estimates use the finite expansion of one half of log((1+z)/(1-z)), with remainder bounded by z^(2n+1)/(1-z^2). Seven terms bound log(t) at the two interval endpoints. Four terms bound log(4(1-t)); the certified log(2) bounds then bound log(1-t).

The profile derivative is one half of log(t)+(1/t^2-1)log(1-t)+1/t. It is negative at the lower endpoint and positive at the upper endpoint. Supporting-line inequalities for the convex profile force every minimizer between those endpoints. A supporting line at the lower endpoint, together with the exact logarithm bounds there, encloses the minimum value. The location and value bounds concern the actual integral, rather than an approximate root equation.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/EntropyMinimum.entropy_minimum_enclosure`
- Dependency: [D5/S3/Arith/FactorialRatio/Compression/EntropyProfile](EntropyProfile.md)
