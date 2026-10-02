# Local Fibonacci Behavior Records

## Abstract

Canonical local records classify every future Fibonacci reading at prime-power precision.

**Definition 1.1 (Reduction of a pair).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.reducePair`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.reducePair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all natural p,H,i and x in (Z/(p^H)Z)^2, reducePair(p,H,i,x) is obtained by applying ZMod.cast into Z/(p^i)Z to each coordinate. For i<=H this is the product of the natural ring homomorphisms.

**Definition 1.2 (The maximal zero-hit layer).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.topHit`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.topHit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all natural p,H,m and x in (Z/(p^H)Z)^2, topHit(p,H,m,x) is the greatest i<=m for which there exists a natural k with the first coordinate of S^k(reducePair(p,H,i,x)) equal to zero. The default value is zero.

**Definition 1.3 (The unit orbit).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.direction`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.direction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all natural p,H,i and x in (Z/(p^H)Z)^2, direction(p,H,i,x) is the orbit of reducePair(p,H,i,x) under simultaneous multiplication of both coordinates by a unit of Z/(p^i)Z. Its interpretation as a primitive projective direction requires a unit coordinate.

**Theorem 1.4 (The zero phase of a primitive state).**

$$\forall (p: \mathbb{N}), \forall (m: \mathbb{N}), \operatorname{Prime}\left(p\right) \implies \forall (x: \operatorname{ZMod}\left(p^{m}\right)^{2}), (\operatorname{IsUnit}\left(\operatorname{fst}\left(x\right)\right) \lor \operatorname{IsUnit}\left(\operatorname{snd}\left(x\right)\right)) \implies \forall (t: \mathbb{N}), \forall (k: \mathbb{N}), \operatorname{fst}\left(\operatorname{iterate}\left(S, t, x\right)\right) = 0 \implies ((\operatorname{fst}\left(\operatorname{iterate}\left(S, k, x\right)\right) = 0) \iff (\operatorname{mod}\left(k, \operatorname{zeroRank}\left(p^{m}\right)\right) = \operatorname{mod}\left(t, \operatorname{zeroRank}\left(p^{m}\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.primitive_hit_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be any prime and m be any natural number. The step S(a,b)=(b,a+b) acts on pairs over Z/(p^m)Z. A pair is primitive when at least one coordinate is a unit. Let r be the least positive index with p^m dividing the Fibonacci number F(r), with F(0)=0 and F(1)=1.

If the first coordinate of S^t(x) is zero, then the first coordinate of S^k(x) is zero exactly when k and t have the same residue modulo r. Both t and k are arbitrary natural numbers, including zero. There is no restriction to odd primes and no assumption that the zero rank grows at every precision.

The coordinates of a primitive pair remain coprime under the step. At a zero hit, the second coordinate is consequently a unit. Forward from this hit, the first coordinate is F(d) times that unit, so its zeros are precisely the multiples of r. A finite common return period transfers this criterion to times before the chosen hit.

**Theorem 1.5 (The low divisibility profile).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.primitive_no_hit_profile`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.primitive_no_hit_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be any prime, H and m be natural numbers with m<=H, and let x and y be pairs over Z/(p^H)Z, each with at least one unit coordinate. Suppose neither reduced pair at precision m has a zero first coordinate at any natural time. The following are equivalent: for every natural k and every i<=m, the first coordinates of S^k(reducePair(p,H,i,x)) and S^k(reducePair(p,H,i,y)) vanish simultaneously; there exists a natural j<m such that both maximal hit layers are j and their unit orbits at layer j are equal. Layer zero has the unique residue pair modulo one. The times include zero.

Simultaneous zero readings at the maximal positive hit layer put both primitive states on the same kernel line. Their unit second coordinates give a common unit multiple after that time, and the common finite return period transports this relation to their initial states. Reduction transports the unit relation to every lower layer. Neither state hits any higher layer, so the maximal layer and its orbit determine every divisibility reading.

**Definition 1.6 (Common saturated depth).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.content`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.content` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all natural p,h and x in (Z/(p^h)Z)^2, content(p,h,x) is the minimum of depth(p,h,val(x.1)) and depth(p,h,val(x.2)), using the integer casts of the natural representatives and the existing saturated-depth function.

**Definition 1.7 (Normalized residue coordinates).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.scaledPair`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.scaledPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all natural p,h,s and x in (Z/(p^h)Z)^2, scaledPair(p,h,s,x) applies eta(p,h,s,-) to each integer representative and retains the residue component, discarding the tag and any depth field. The resulting pair is over Z/(p^(h-s))Z. When s is at most each coordinate depth, both eta values use their high branch and retain the quotients by p^s.

**Definition 1.8 (Three record types).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.LocalLabel`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.LocalLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all natural p,h,e, a LocalLabel(p,h,e) is one of three disjoint records. High retains a pair over Z/(p^h)Z. NoHit retains natural s,j and an optional unit-orbit set over (Z/(p^j)Z)^2. Hit retains natural s,t, a residue A over Z/(p^h)Z and a residue U over Z/(p^ell)Z, where ell=h-s-c, c is the p-adic valuation of F(zeroRank(p^(e-s))), and subtraction is saturated natural subtraction.

**Definition 1.9 (Canonical local records).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.localLabel`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.localLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all natural p,h,e and x in (Z/(p^h)Z)^2, put s=content(p,h,x). If e<=s, the record is High(x), including the zero pair. Otherwise set u=scaledPair(p,h,s,x) and m=e-s. If the reduction of u to precision m has a zero first coordinate at some natural time, choose its least such time t and return Hit(s,t,(S^t(x)).1,U), where U is the second coordinate of scaledPair(p,h,s,S^t(x)) reduced to the prescribed exponent ell. If there is no hit, put j=topHit(p,h-s,m,u) and return NoHit(s,j,None) for j=0, or NoHit(s,j,Some(direction(p,h-s,j,u))) otherwise. The local classification below identifies equality of these records with equality of all future psi readings.

**Theorem 1.10 (Complete local behavior classification).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prime p, every natural h>=1, every natural e<=h, and all x,y in (Z/(p^h)Z)^2, the following are equivalent: for every natural k>=0, psi(p,h,e,val(fst(S^k(x)))) equals psi(p,h,e,val(fst(S^k(y)))); localLabel(p,h,e,x) equals localLabel(p,h,e,y). Here S(a,b)=(b,a+b), and psi retains the saturated depth when it is below e and the full residue modulo p^h otherwise. The statement includes e=0, p=2, the zero pair, and the unique scalar residue at precision zero.

The readings at times zero and one recover the common saturated depth of the pair. In the High case both coordinates are retained, so equality of all readings is exactly equality of the pair. For a low pair, division by its common power of p gives primitive coordinates; reduction of those coordinates to layer i vanishes exactly when the original coordinate depth is at least s+i.

For NoHit records, the maximal hit layer and its unit orbit determine every lower-layer zero test. No higher-layer test occurs. These tests determine each depth below e, and hence every psi reading. Conversely the complete depth profile recovers that maximal layer and its direction, with the single empty-direction record at layer zero.

For Hit records, simultaneous layer-e-s hits recover the least nonnegative phase t. The primitive zero-phase theorem also determines all lower-layer depth tests. At times t and t+r, where r=zeroRank(p^(e-s)), the readings retain complete residues. The first recovers A, and cancellation of F(r) from the second recovers B/p^s modulo p^(h-s-v_p(F(r))). The full valuation is used even when zero-rank lifting is stationary. Equality of these first two samples gives equality at every coarse-clock time by the sampling quotient theorem; t<r identifies precisely all nonnegative hit times. The remaining times are determined by the lower-layer depth tests.

Prime-power Fibonacci zero ranks are treated in Wall (1960), Robinson (1963), and Bragman and Rowland, arXiv:2202.00704v2. The classification uses those zero-rank properties together with finite orbit and sampling identities, without an assumption that the rank multiplies by p at each lift.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.LocalLabel`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.content`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.direction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.localLabel`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.primitive_hit_phase`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.primitive_no_hit_profile`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.reducePair`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.scaledPair`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.topHit`
- Dependency: [D5/S3/Arith/FibonacciAtomic/GraftAffineClosure](GraftAffineClosure.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/PrimePowerGcdHorizon](PrimePowerGcdHorizon.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SamplingQuotient](SamplingQuotient.md)
