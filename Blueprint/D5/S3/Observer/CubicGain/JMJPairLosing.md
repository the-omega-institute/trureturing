# Complete losing pairs below JMJ

## Abstract

Complete losing pairs below JMJ

**Theorem 1.1 (Native failure at either fourth JMJ child).**

Lean statement: `D5/S3/Observer/CubicGain/JMJPairLosing.jmj_pair_losing_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/JMJPairLosing.jmj_pair_losing_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n be any natural number at least three, E either fourth action, and z and v arbitrary real numbers. Let W and Z be distinct complete legal cubic-gain worlds whose actual chronological JMJE readings are exactly (0,24,48,z,v). There is no source, drift, gain-ray or individual nonzero-sample promise. The same two-world support has native Losing n exactly when the drifts agree, both gains vanish at every original clock 4+j for 2 <= j <= n, and the actual fifth responses agree under each of J and M.

For n=3 the zero condition consists precisely of gW(6)=gZ(6)=gW(7)=gZ(7)=0. Equality along every continuation forces common drift and the later zero gain samples. Equal sources would identify the coefficient vectors from the four shared ancestor readings at clocks zero through three, since every actual source trace there is positive; hence distinct worlds have distinct sources. The reverse implication constructs every entire response slice recursively: the common fifth value retains both worlds, and each later value is their common drift. Every node retains the two-world stopping guard.

The characterization applies to both fourth children and all real z,v. It does not classify the quadratic roots at fourth J, determine the admissible interval or forced fourth response, exclude fourth M, or extract a losing pair from a larger support.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/JMJPairLosing.jmj_pair_losing_iff`
- Dependency: [D5/S3/Observer/CubicGain/MixedTripleExclusion](MixedTripleExclusion.md)
