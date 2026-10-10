# Actual gcd-six source reduction

## Abstract

The native Divisor Nim moves give a four-lookback recurrence, exact zero phases, a four-letter odd alphabet and the actual fixed-follower forcing for every positive fixed multiset of greatest common divisor six.

**Theorem 1.1 (Move reconstruction and zero-anchor dynamics).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGcdSixSource.gcd_six_source_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimGcdSixSource.gcd_six_source_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a positive nonempty multiset A of greatest common divisor six. The varying heap is n, and f(n) is the native Grundy value of the multiset obtained by adjoining n to A. Occurrences retain their multiplicities throughout.

A fixed move selects one occurrence h in A and removes a positive amount d at most h that divides every other fixed heap. It is legal after adjoining n exactly when d also divides n. There is no requirement that d divide h. The changed heap h minus d is omitted when zero. F(n), defined by fixedValues, contains the Grundy values of precisely the nonempty fixed followers with n adjoined.

For n greater than twice the sum of A, f(n) is the mex of F(n) together with f(n minus 1), f(n minus 2), f(n minus 3), and f(n minus 6). These are all positive divisors of six. An empty fixed follower contributes the singleton value n. The native bound puts the parent value below n, so omitting that follower does not change the mex.

Let c count the fixed heaps of dyadic depth one. The zero phase is zero modulo four when c is even and two modulo four when c is odd. The native minimum-depth outcome theorem proves this for every positive n. For odd n greater than twice the sum of A plus six, each legal fixed move creates exactly two odd heaps and hence has value zero; removal of one supplies such a nonempty follower. Thus F(n) is the singleton zero. One of the two even lookbacks is also zero, giving odd values between one and four.

At a zero anchor t greater than twice the sum of A plus ten, put u=f(t minus 3), v=f(t minus 1), and w=f(t plus 1). These are in the alphabet one through four, with u different from v and v different from w. Removal of two proves both inequalities. With b=f(t plus 2) and y=f(t plus 3), the actual block formulas are b=mex(F(t plus 2) union {0,v,w}), y=mex{0,b,w,u}, and f(t plus 5)=mex{0,y,b,v}. In particular the six-step predecessors remain present.

For H bounding every fixed heap, sixTargetPeriod is twice the least common multiple of one through H. If every actual nonempty direct fixed follower has this eventual period, the whole set F has the same eventual period. A common tail start exists because there are finitely many direct followers, and every legal fixed removal divides the specified period. The period is divisible by four.

The parent tail follows by the finite transition argument below. It uses the finite transition projection, arbitrary-word closure and stabilization, and reconstruction of all actual values from the stabilized return state. The unrestricted equation (21) remains open.

**Theorem 1.2 (The specified parent period after three returns).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGcdSixSource.gcd_six_parent_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimGcdSixSource.gcd_six_parent_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be any positive multiset with greatest common divisor six, let H bound every heap in A, and put T=2 times lcm(1,...,H). Assume that every actual nonempty direct fixed follower Q has an eventual T-periodic sequence g(n adjoined to Q). Then g(n adjoined to A) also has an eventual T-periodic tail. There is no bound on heap count or multiplicity.

The odd triple (u,v,w) occupies the 36 states in one through four with u different from v and v different from w. At each zero anchor, project F(t plus 2) to membership at one, two, three and four. If its first mex b is at least five, replacing b by five preserves both following mexes, whose values are at most four. The resulting 16 masks act through seven generators, represented by masks 0,1,2,3,5,6,7.

The explicit transformation family has 48 rows. It contains identity and is closed under all seven generators, with composition ordered by applying each appended generator to the previous output. Every row R satisfies R to the fourth power equals R to the third power at all 36 states. Induction over arbitrary word length therefore gives this identity for every finite composition, with no bound on T.

The actual coefficient sets repeat after T, and four divides T. A T interval thus repeats the same ordered word of T divided by four generators. After three returns its actual state is fixed by that word. Equal state coordinates reconstruct both odd positions; the full, unprojected coefficient sets recover the intervening even mex. The remaining even position is an actual zero phase. These identities cover every parent value in the tail and give T itself, rather than a multiple of T.

This is the unrestricted gcd-six parent implication in the induction strategy. It keeps the direct-follower hypothesis explicit and does not settle all cases of equation (21).

The source-reduction information registration is validated. The parent information audit remains unfinished under the CLAUDE section 3.9 linked-issue exception: the faithful actual law and equivalence compile, while a failure-of-law realization and whole-family sensitivity remain unpaid. See https://github.com/the-omega-institute/trureturing/issues/15071.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGcdSixSource.gcd_six_parent_tail`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGcdSixSource.gcd_six_source_reduction`
- Dependency: [D5/S3/Combinatorics/Games/DivisorNimBound](DivisorNimBound.md)
