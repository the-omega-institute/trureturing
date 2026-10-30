# Unsigned Golden Readout

## Abstract

Unsigned golden expansions on infinite legal digits.

Let L be SuccessorContinuity.LegalDigits: Boolean streams x with no adjacent ones, carrying the subspace topology inherited from the product of discrete Boolean spaces. Put phi=(1+sqrt(5))/2 and r=phi inverse. Positions start at zero; the weight of position k is r to the power k+1. All sums below are infinite real sums. The symbols u and v denote the existing legal streams 101010... and 010101... respectively.

**Definition 1.1 (The unsigned series).**

$$\forall x \in L,\; U\left(x\right) = tsum\left((k:Nat \mapsto if\left(val\left(x, k\right), 1, 0\right) \cdot r^{k + 1})\right)$$

*Formalization.* `D5/S1/Digit/Infinite/UnsignedGoldenReadout.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient is one for a true digit and zero for a false digit. Thus the first coefficient has weight r, with no alternating sign.

**Definition 1.2 (The zero name).**

$$\forall k \in Nat,\; val\left(zeroName, k\right) = false$$

*Formalization.* `D5/S1/Digit/Infinite/UnsignedGoldenReadout.zeroName` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every digit of zeroName is false.

**Definition 1.3 (A single occupied position).**

$$\forall k \in Nat,\; val\left(singleName, k\right) = decide\left(k = 0\right)$$

*Formalization.* `D5/S1/Digit/Infinite/UnsignedGoldenReadout.singleName` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The only true digit of singleName is position zero, so its sequence is 1000....

**Theorem 1.4 (Continuous interval readout and prefix estimate).**

$$(\forall x \in L,\; Summable\left((k:Nat \mapsto if\left(val\left(x, k\right), 1, 0\right) \cdot r^{k + 1})\right)) \land (range\left(U\right) = Icc\left(0, 1\right)) \land (Continuous\left(U\right)) \land (\forall n \in Nat,\; \forall x \in L,\; \forall y \in L,\; ((\forall k \in Nat,\; (k < n \Rightarrow val\left(x, k\right) = val\left(y, k\right))) \Rightarrow abs\left(U\left(x\right) - U\left(y\right)\right) \le r^{n})) \land (U\left(zeroName\right) = 0) \land (U\left(u\right) = 1) \land (singleName \neq v) \land (U\left(singleName\right) = r) \land (U\left(v\right) = r)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/UnsignedGoldenReadout.unsigned_golden_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every legal stream gives a summable series. Its range is exactly the closed unit interval, and the readout is continuous in the inherited topology. For every natural n, including zero, agreement at each position k<n bounds the absolute difference of the readouts by r to the power n. The zero name and u realize the endpoints. The distinct names singleName and v both read r.

To bound the range, group positions 2k and 2k+1. Legality permits at most one occupied position in each pair. Its contribution is at most r(r squared) to the power k, whose sum is one because r squared+r=1. The alternating stream u attains this bound.

For a real t in [0,1], start with residual t. At a residual z, choose digit one when z>r and replace z by (z-r)/r; otherwise choose zero and replace z by z/r. Every residual stays in [0,1]. A one leaves a residual at most r, so the next digit is zero. The first n terms sum to t minus r to the power n times the nth residual. This remainder tends to zero, proving surjectivity, including the boundary points.

Deleting n initial digits leaves another legal stream. Splitting the series gives the common prefix sum plus r to the power n times the shifted readout. Both shifted readouts lie in [0,1], giving the prefix estimate. Continuity also follows from the summable geometric bound on the continuous coordinate functions. A leading zero scales the tail readout by r; a leading 10 sends it to r+r squared times the tail readout. These branch intervals are [0,r] and [r,1], and cover [0,1].

The endpoint and coincident-name values follow by summing the even and odd geometric subseries. In particular U(u)=1 and U(v)=r, whereas the single occupied position also has value r. These are unsigned beta expansions; no uniqueness of names or mathematical novelty is asserted.

## References

- Truth anchor: `D5/S1/Digit/Infinite/UnsignedGoldenReadout.U`
- Truth anchor: `D5/S1/Digit/Infinite/UnsignedGoldenReadout.singleName`
- Truth anchor: `D5/S1/Digit/Infinite/UnsignedGoldenReadout.unsigned_golden_readout`
- Truth anchor: `D5/S1/Digit/Infinite/UnsignedGoldenReadout.zeroName`
- Dependency: [D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel](ClosedObservationCommonTailWidthModel.md)
- Dependency: [D5/S1/Digit/Infinite/SignedSeriesRange](SignedSeriesRange.md)
