# Native common-cut two-negative joint lift

## Abstract

For every asymmetric pair of dyadic exponents, the actual old source and the actual doubled source admit full physical permutations at one shared cut.

**Theorem 1.1 (Native common-cut two-negative joint lift).**

Lean statement: `D5/S3/Combinatorics/Circle/TwoNegativeJointLift.actualSource_two_negative_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/TwoNegativeJointLift.actualSource_two_negative_joint_lift`. ∎

*Source.* Repository-derived Section 46 constructor.

*Commentary.*

For `a>b>=2`, set `k=a+b`, `q=2^a`, `r=2^b`, `N=qr-1`, and `v=q+1`. The physical labels are kept distinct even when their numerical values agree. The old source has the U ladder, the alpha negative, the V ladder and the beta negative; the new source has the corresponding doubled physical labels and one fresh label of value `v`.

The selector chooses one literal V-ladder support with `w=floor((N-v)/(2r+1))`. Its old mass is `(r+1)w` and its new mass is `(2r+1)w`, on the same physical support. The complementary positives are consumed in the same word. The cases `q=2r` and `q>=4r` use the shared cut respectively before beta after the common rotation and before beta in the direct order. Every natural prefix, including empty, full and overlong prefixes, is covered by the native `InStrip` witness.

This is a source-level common-cut constructor. It does not establish nonzero phase transport, a numerical-period quotient, or the full Circle C3.1 problem.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/TwoNegativeJointLift.actualSource_two_negative_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/SourceWidth](SourceWidth.md)
- Dependency: [D5/S3/Combinatorics/Circle/PeriodicShortening](PeriodicShortening.md)
- Dependency: [D5/S3/Combinatorics/Circle/RunFirstEarTransport](RunFirstEarTransport.md)
