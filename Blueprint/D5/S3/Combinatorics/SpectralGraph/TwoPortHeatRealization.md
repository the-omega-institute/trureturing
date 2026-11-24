# A physical order gap for two calibrated heat ports

## Abstract

A complete two-port heat network has stationary-inclusive linear order five and physical order six.

**Theorem 1.1 (Moments through degree four force six physical vertices).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/TwoPortHeatRealization.exact_order_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/TwoPortHeatRealization.exact_order_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use four hidden coordinates. Add the all-ones vector divided by 1000 to each of the incidence vectors x=(1,1,0,0), y=(0,1,1,0), u=(0,0,1,1), and v=(1,0,0,1). Put X=[x,y], P=uuᵀ+vvᵀ, and D=4I−P. With q=1001/250000, the hidden ground is g=(x+y)/4+P(x+y)/(4(1−2q)). The port block C has diagonal entries 1+xᵀg and 1+yᵀg and off-diagonal entries −1. The generator S has blocks C, −Xᵀ, −X, and D. Its positive ground z=(1,1,g) gives rational masses zᵢ² and conductances −zᵢSᵢⱼzⱼ, strictly positive for distinct vertices.

For the port insertion E, let Uⱼ=EᵀSʲE. The first three block columns [E,SE,S²E] have a nonzero minor of order five. Their Gram is the three-block Hankel matrix, whose rank is five. The port space and the hidden hyperplane h₀−h₁+h₂−h₃=0 form an invariant space of dimension five containing every generator iterate of E. The restriction realizes the same heat response Eᵀ exp(−tS) E. Equality at positive times extends to all real times by analyticity, and differentiation at zero gives equal moments. The same Hankel matrix factors through the states of any finite real linear realization, which therefore needs at least five states.

Matching U₀ through U₄ fixes the hidden Gram of F=[X,PX]. For a candidate with at most three hidden vertices, the Gram makes the columns of [X,g] span the hidden space. To see this, first use the target coefficients of g in F. For the candidate, the equations Xᵀg=C1 and Dg=X1 determine Fᵀg from the matched data. The spanning property makes Fᵀ injective, so the candidate ground has exactly those coefficients. Now P on X is known from F and Pg=4g−X1. The resulting quadratic form of P on [X,g] agrees with the target's and is nonnegative. This gives a nonnegative diagonal for P. The physical sign of D gives nonnegative off-diagonal entries, and X is entrywise nonnegative as well.

In cyclic order [x,y,Py,Px], the actual Gram has diagonals at most 4, cyclic entries at least 1, and both opposite entries 2q(1+q)<1/36. FourPortHeatRealization.cycle_gram_width forces any entrywise nonnegative factor of this Gram to have at least four hidden coordinates. This rules out all physical candidates with at most five total vertices, allowing arbitrary positive hidden masses and zero candidate conductances. The same bound applies to the full calibrated heat response, and the explicit complete generator attains it.

The rational witness and order calculation are from the two-port-exact-order research note. The conserved-ground argument uses the fourth-moment obstruction in the short-time research note. The cycle-width proof is reused from FourPortHeatRealization, which credits Shaked-Monderer for the classical support argument.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwoPortHeatRealization.exact_order_gap`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/FourPortHeatRealization](FourPortHeatRealization.md)
