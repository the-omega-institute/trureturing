# The complete native JMJ pair classification

## Abstract

The complete native JMJ pair classification

The native histories use original clocks and chronological left multiplication. Writing j=P(0,1)+P(1,0), ell=1+P(0,1), and T=P(0,0)+j, the actual fourth traces are ell for J and 2ell-1 for M. Their fifth J and M traces are respectively T and j+ell after fourth J, and 2T-j and T+2ell-1 after fourth M. These are alternative responses of one fixed complete world. Only the chosen action and its immediate reading are acquired.

**Definition 1.1 (The source quadratic).**

Lean statement: `D5/S3/Observer/CubicGain/JMJRootPair.q`

*Formalization.* `D5/S3/Observer/CubicGain/JMJRootPair.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a and B, q(a,B)=B^2-(a+4/5)B+6a/5-a^2.

**Definition 1.2 (The discriminant).**

Lean statement: `D5/S3/Observer/CubicGain/JMJRootPair.discriminant`

*Formalization.* `D5/S3/Observer/CubicGain/JMJRootPair.discriminant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real a, discriminant(a)=5a^2-16a/5+16/25.

**Definition 1.3 (The lower root).**

Lean statement: `D5/S3/Observer/CubicGain/JMJRootPair.lowerRoot`

*Formalization.* `D5/S3/Observer/CubicGain/JMJRootPair.lowerRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real a, lowerRoot(a)=(a+4/5-sqrt(discriminant(a)))/2.

**Definition 1.4 (The upper root).**

Lean statement: `D5/S3/Observer/CubicGain/JMJRootPair.upperRoot`

*Formalization.* `D5/S3/Observer/CubicGain/JMJRootPair.upperRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real a, upperRoot(a)=(a+4/5+sqrt(discriminant(a)))/2.

**Definition 1.5 (The unnormalized source).**

Lean statement: `D5/S3/Observer/CubicGain/JMJRootPair.rootMatrix`

*Formalization.* `D5/S3/Observer/CubicGain/JMJRootPair.rootMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a and B, rootMatrix(a,B) is the matrix with consecutive rows (a,B) and (4/5-B,6/5-a-B).

**Definition 1.6 (The source trace).**

Lean statement: `D5/S3/Observer/CubicGain/JMJRootPair.rootScale`

*Formalization.* `D5/S3/Observer/CubicGain/JMJRootPair.rootScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real B, rootScale(B)=6/5-B. This is the trace of rootMatrix(a,B).

**Definition 1.7 (An interior quadratic root).**

Lean statement: `D5/S3/Observer/CubicGain/JMJRootPair.RootData`

*Formalization.* `D5/S3/Observer/CubicGain/JMJRootPair.RootData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a and B, RootData(a,B) means 0<B<4/5 and q(a,B)=0.

**Definition 1.8 (The complete root world).**

Lean statement: `D5/S3/Observer/CubicGain/JMJRootPair.rootWorld`

*Formalization.* `D5/S3/Observer/CubicGain/JMJRootPair.rootWorld` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real a with 0<a<2/5 and every real B satisfying RootData(a,B), rootWorld(a,B) is a native World3. Its source is rootScale(B) inverse times rootMatrix(a,B), its entire coefficient vector in ascending order is (0,42s,-13s,s), where s=rootScale(B), and its drift is zero. Thus its gain polynomial is s times t(t-6)(t-7). The source has strictly positive entries, rank one and trace one, and the whole coefficient vector is nonzero.

**Definition 1.9 (The lower complete world).**

Lean statement: `D5/S3/Observer/CubicGain/JMJRootPair.lowerWorld`

*Formalization.* `D5/S3/Observer/CubicGain/JMJRootPair.lowerWorld` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real a with 0<a<2/5, lowerWorld(a) is rootWorld(a,lowerRoot(a)). The lower root is strictly between zero and 4/5 and satisfies the quadratic equation.

**Definition 1.10 (The upper complete world).**

Lean statement: `D5/S3/Observer/CubicGain/JMJRootPair.upperWorld`

*Formalization.* `D5/S3/Observer/CubicGain/JMJRootPair.upperWorld` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real a with 0<a<2/5, upperWorld(a) is rootWorld(a,upperRoot(a)). The upper root is strictly between zero and 4/5 and satisfies the quadratic equation.

**Theorem 1.11 (The two actual root worlds).**

Lean statement: `D5/S3/Observer/CubicGain/JMJRootPair.canonical_pair_losing`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/JMJRootPair.canonical_pair_losing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a with 0<a<2/5, lowerWorld(a) and upperWorld(a) are distinct. Each has the actual chronological JMJJ reading array (0,24,48,36(a+4/5),144/5), and the two-world support has native Losing 3 at that fourth child. The fifth J response is 10(a+4/5) on both worlds, the fifth M response is 20 on both worlds, and the gains vanish at clocks six and seven. Every response slice through original clock seven retains both worlds and the stopping guard.

**Definition 1.12 (The unordered pair at the third reading).**

Lean statement: `D5/S3/Observer/CubicGain/JMJRootPair.canonicalPair`

*Formalization.* `D5/S3/Observer/CubicGain/JMJRootPair.canonicalPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real z with 144/5<z<216/5, canonicalPair(z) is the finite set consisting of lowerWorld(z/36-4/5) and upperWorld(z/36-4/5). Both worlds have exactly the source, whole gain polynomial and drift specified above.

**Theorem 1.13 (The complete JMJJ pair classification).**

Lean statement: `D5/S3/Observer/CubicGain/JMJRootPair.jmjj_pair_losing_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/JMJRootPair.jmjj_pair_losing_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real z and v and all distinct native complete worlds W and Z, assume that each actual chronological JMJJ reading array is (0,24,48,z,v). Then native Losing 3 for the finite set {W,Z} at JMJJ holds if and only if 144/5<z<216/5, v=144/5, and {W,Z}=canonicalPair(z). The interval proof is carried as the parameter of canonicalPair. The worlds range over the full World3 domain: strictly positive rank-one trace-one sources, arbitrary real drift, and every nonzero entire real polynomial of degree at most three. No source distinction, gain ray or individual nonzero sample is assumed.

**Theorem 1.14 (No actual fourth M pair loses for three steps).**

Lean statement: `D5/S3/Observer/CubicGain/JMJRootPair.jmjm_pair_not_losing`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/JMJRootPair.jmjm_pair_not_losing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real z and v and all distinct native complete worlds W and Z whose actual chronological JMJM reading arrays both equal (0,24,48,z,v), native Losing 3 for {W,Z} at JMJM is false. This uses the same complete World3 domain, with arbitrary drift, gain signs, lower degrees and zero samples.

A distinct losing pair has common drift d and both gains vanish at six and seven. Its whole gains are (t-6)(t-7)(beta*t-d/42). Equal leading coefficients would determine the same source and complete world: a nonzero second or fourth sample fixes ell, and either the fifth responses or the first and third ancestors fix j and T. Therefore the leading coefficients differ. At fourth J the shared second and fourth responses force d=0. The weighted sources beta*P have exactly the displayed rootMatrix form; rank one supplies q(a,B)=0. Two distinct positive roots below 4/5 force 0<a<2/5. Conversely the discriminant is positive and both explicit roots lie strictly inside (0,4/5); the source chart proves full legality of both worlds. Quadratic exhaustion then identifies the unordered pair.

At fourth M put x=gW(2), y=gZ(2). Both are nonzero, different, and have positive product. The early first and third gain samples are also nonzero consequences of the histories. The actual fourth equality gives d(48-d)/(7xy)=-3/10. The two actual fifth equalities give d(z-d)/(35gW(3)gZ(3))=1/20 and d(24-d)/(7gW(1)gZ(1))=1/10. The first identity forces d<0 or d>48; the last contradicts gW(1)gZ(1)>0. No fourth or fifth gain sample is divided out. The conclusions concern two-target sets only.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/JMJRootPair.RootData`
- Truth anchor: `D5/S3/Observer/CubicGain/JMJRootPair.canonicalPair`
- Truth anchor: `D5/S3/Observer/CubicGain/JMJRootPair.canonical_pair_losing`
- Truth anchor: `D5/S3/Observer/CubicGain/JMJRootPair.discriminant`
- Truth anchor: `D5/S3/Observer/CubicGain/JMJRootPair.jmjj_pair_losing_iff`
- Truth anchor: `D5/S3/Observer/CubicGain/JMJRootPair.jmjm_pair_not_losing`
- Truth anchor: `D5/S3/Observer/CubicGain/JMJRootPair.lowerRoot`
- Truth anchor: `D5/S3/Observer/CubicGain/JMJRootPair.lowerWorld`
- Truth anchor: `D5/S3/Observer/CubicGain/JMJRootPair.q`
- Truth anchor: `D5/S3/Observer/CubicGain/JMJRootPair.rootMatrix`
- Truth anchor: `D5/S3/Observer/CubicGain/JMJRootPair.rootScale`
- Truth anchor: `D5/S3/Observer/CubicGain/JMJRootPair.rootWorld`
- Truth anchor: `D5/S3/Observer/CubicGain/JMJRootPair.upperRoot`
- Truth anchor: `D5/S3/Observer/CubicGain/JMJRootPair.upperWorld`
- Dependency: [D5/S3/Observer/CubicGain/JMJPairLosing](JMJPairLosing.md)
