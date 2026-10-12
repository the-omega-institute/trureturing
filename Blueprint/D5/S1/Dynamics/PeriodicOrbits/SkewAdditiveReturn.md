# Additive Skew Dynamics and Orbit Holonomy

## Abstract

The accumulated charge on one base cycle determines every lifted return.

Let X be any type, A an additive commutative group, f a self-map of X, and c a function from X to A. Neither finiteness nor invertibility is assumed. For x in X, a in A and a natural time n, write S(n,x) for the Mathlib Birkhoff sum of c along the first n iterates of f. Natural scalar multiplication in A is written as a centered dot. The zeroth iterate is the identity.

$$
S(n,x)=\sum_{j<n}c(f^{j}x)
$$

**Definition 1.1 (The state-dependent update).**

$$T(x,a)=(f(x),a+c(x))$$

*Formalization.* `D5/S1/Dynamics/PeriodicOrbits/SkewAdditiveReturn.skewStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The charge is evaluated at the current state, before f advances the base. The fiber is translated by that charge. A translation is invertible even when the base self-map is not.

**Theorem 1.2 (Transport along the actual orbit).**

$$T^{n}(x,a)=(f^{n}x,a+S(n,x))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/SkewAdditiveReturn.skew_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This identity holds for every natural n. Induction uses the actual update: after n steps the next charge is c at f iterated n times on x. The successor identity for the Birkhoff sum adds precisely this term.

**Theorem 1.3 (A returning block acts by one translation).**

$$f^{p}x=x\Rightarrow T^{pk}(x,a)=(x,a+k\cdot S(p,x))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/SkewAdditiveReturn.skew_iterate_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural p and k, a base return after p steps makes every repeated p-block start at the same x. Its charge h equals S(p,x). Induction on the number of blocks gives translation by k times h. This statement permits p equal to zero and nonminimal positive p. At a block time, the full state returns exactly when k times h is zero. A nonminimal p does not determine the global minimum: for a fixed base with zero charge, p equal to two is a returning block although the minimum is one.

For the next two statements, p denotes minimalPeriod f x and h denotes S(p,x). Mathlib records a minimal period of zero when there is no positive return, and an additive order of zero for an element of infinite order. The equalities below include those conventions, as well as time zero.

**Theorem 1.4 (Exact lifted returns).**

$$T^{n}(x,a)=(x,a)\Leftrightarrow p\cdot\operatorname{addOrderOf}(h)\mid n$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/SkewAdditiveReturn.skew_return_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projecting a lifted return to X forces p to divide n. Write n as p times k. The block formula then reduces the remaining equality to k times h being zero, which is equivalent to addOrderOf h dividing k. Conversely, that divisibility cancels the block translation. When p is positive, this is equivalently p dividing n and (n divided by p) times h equal to zero.

**Theorem 1.5 (The exact minimum).**

$$\operatorname{minimalPeriod}(T,(x,a))=p\cdot\operatorname{addOrderOf}(h)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/SkewAdditiveReturn.skew_minimalPeriod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The return-time sets are exactly the multiples of p times addOrderOf h, so divisibility in both directions identifies the minimum. For positive p, finite holonomy order multiplies the base cycle length, while infinite holonomy order excludes every positive lifted return. Zero holonomy has order one and leaves the minimum at p. If the base has no positive return, p is zero and the lift has none either.

## Group actions and arithmetic consequences

On a periodic base orbit, f restricts to a cyclic permutation. Its skew lift on that orbit times A is invertible: retreat one base step and subtract the charge at the predecessor. Hence integer iterates act there, and the p-step return map on the fiber over x is translation by h. The stabilizer of this translation action is the set of integers killing h. A global integer action on all of X times A requires f to be a permutation; the theorems about natural iterates do not assert one.

For A equal to ZMod q with q positive, choose the canonical natural representative h.val. Mathlib's ZMod.addOrderOf_coe gives the multiplier q divided by gcd(q,h.val). This includes q equal to one and h equal to zero, both giving multiplier one. In ZMod 2 the multipliers are one and two, so the lift of a minimal base p-cycle has minimum p or 2p according to whether the accumulated charge is zero or one. Taking the charge of a binary sequence to be one minus its current digit makes this sum the parity of the zero count. Exchanging the product coordinates relates this formula to the anchored shift, once its stated update is identified.

ZMod 0 is the integers. In an integer fiber, zero h gives minimum p; nonzero h has infinite additive order and prevents every positive return. For signed prime ledgers, each coordinate is also an integer and a nonzero ledger has infinite additive order. The existing equivalence signed_prime_ledger_equiv_positive_rationals transports addition of exponents to multiplication of positive rationals: a block multiplies by its associated rational, and only the identity multiplier permits a positive return. This is a consequence for any dynamics whose actual update has been identified with the skew update; it does not construct a concrete arithmetic dynamics.

A potential difference charge telescopes on a returning base path and has zero holonomy. On a connected path groupoid, an A-valued path cost that adds under composition and changes sign under inversion has zero cost on every loop exactly when it is a difference of vertex potentials. The existing closed_path_zero_iff_exists_potential gives this gauge principle. A raw closed ChargedCarryPath has zero potential difference. In contrast, carryCharge_not_determined_by_fixed_modulus supplies, for each fixed modulus at least two, equal residues with different signed carry charges, so it forbids inferring a residue-defined charge from those residues alone. An arithmetic application must verify the update and any claimed descent. Noncommutative fiber groups require ordered products in place of these commutative sums.

## References

- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/SkewAdditiveReturn.skewStep`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/SkewAdditiveReturn.skew_iterate`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/SkewAdditiveReturn.skew_iterate_block`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/SkewAdditiveReturn.skew_minimalPeriod`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/SkewAdditiveReturn.skew_return_iff`
