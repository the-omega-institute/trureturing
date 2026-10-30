# Zero drift and terminal gain

## Abstract

Zero drift excludes a zero terminal gain in the full original parent

An original parent is one strict source P=[[r,b],[r(1-r)/b,1-r]], one nonzero real polynomial g of degree at most three, and one actual drift d. The chronological five readings are exactly (0,24,147/5,24,18). Every such world with d=0 has g(7)≠0.

Put j=b+r(1-r)/b, n=j+r, T=1+b and u=1+2b. The original-world coordinate correspondence reconstructs the whole gain from its values at clocks zero through three. The fourth reading and the hypothetical equality g(7)=0 give 96/j−882/(5T)+96/n=18/u and 1680/j−12348/(5T)+840/n=0. Positivity of the source makes all these denominators positive.

Solving these two equations gives 3(269u−25)j=400u(u+1) and 3(123u+25)n=200u(u+1). Since n=j+r, subtraction yields 3(123u+25)(269u−25)r=200u(u+1)(23u−75). Thus r>0 forces u>75/23. For u≥27, the two denominator factors are smaller than 131u and 269u, whereas the right side is at least 109200u²; this contradicts r<1 because 3·131·269=105717. Hence u<27.

For c=r(1-r)/b=j−b the first equation now gives 6(269u−25)c=−7u²+1682u−75. On 75/23<u<27 the numerator exceeds 1470u and the positive denominator is smaller than 1614u. Consequently c>245/269 and b>26/23, so bc>6370/6187. This contradicts bc=r(1-r)≤1/4.

The exclusion concerns every strict original world realizing those five rows. No later acquired readings, response chart, regularity condition, exact gain degree, or additional nonzero sampled gain enters the statement. All four ordinary polynomial coefficients are unrestricted apart from the original conditions. The result is a derivation for this matrix observation model and makes no physical realization or literature priority claim.

**Theorem 1.1 (Zero drift excludes terminal gain zero).**

Lean statement: `D5/S3/Observer/CubicGain/ZeroDriftExclusion.original_zero_drift_terminal_gain_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/ZeroDriftExclusion.original_zero_drift_terminal_gain_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every OriginalWorld W satisfying OriginalParent W, actual drift W.2.2.1=0 implies (originalPolynomial W).eval 7≠0. This includes every nonzero gain polynomial of degree at most three and all strict original sources.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/ZeroDriftExclusion.original_zero_drift_terminal_gain_ne_zero`
- Dependency: [D5/S3/Observer/CubicGain/OriginalWorld](OriginalWorld.md)
