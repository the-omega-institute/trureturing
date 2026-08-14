# Dedekind Reciprocity by Finite Sums

## Abstract

Dedekind reciprocity follows from exact finite residue sums and a coprime lattice-point exchange.

The proof uses only exact rational arithmetic. It rewrites the frozen phase-1 sawtooth through reduced residues, evaluates the linear and square residue sums, converts the cross term by Euclidean division, and double-counts the two strict triangles in a coprime lattice rectangle.

**Theorem 1.1 (Dedekind reciprocity).**

$$\forall c, d\in \mathbb{N},\ c>0 \land d>0 \land \gcd(c, d)=1 \Rightarrow \operatorname{dedekindSum}(d, c) + \operatorname{dedekindSum}(c, d) = -\frac{1}{4} + \frac{\frac{c}{d} + \frac{d}{c} + \frac{1}{cd}}{12}.$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DedekindReciprocity.dedekind_reciprocity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The named ladder is sawtooth_div_eq_mod and dedekindSum_eq_mod_sum; sum_Ico_cast, sum_Ico_cast_sq, and sum_mul_mod; sum_div_gauss, latticeDifference_closed, and weightedFloorSum_exchange; followed by dedekindSum_eq_residueCrossTerm and the final rational assembly.

Coprimality is used to permute the nonzero residues and to exclude diagonal points from the lattice rectangle. No analytic convergence or continued-fraction induction enters this theorem.

**Theorem 1.2 (The exact three-four reciprocity check).**

$$\operatorname{dedekindSum}(3, 4) + \operatorname{dedekindSum}(4, 3) = -\frac{5}{72}.$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DedekindReciprocity.dedekind_reciprocity_three_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the coprime pair three and four, the two exact rational sums total minus five seventy-seconds; together with the frozen value dedekindSum(3,4) = -1/8, this gives dedekindSum(4,3) = 1/18.

## References

- Truth anchor: `D5/S1/Phase/Interference/DedekindReciprocity.dedekind_reciprocity`
- Truth anchor: `D5/S1/Phase/Interference/DedekindReciprocity.dedekind_reciprocity_three_four`
- Dependency: [D5/S1/Phase/Interference/DedekindBhkCertificates](DedekindBhkCertificates.md)
- Dependency: [D5/S1/Phase/Interference/DedekindReciprocityFiniteSums](DedekindReciprocityFiniteSums.md)
- Dependency: [D5/S1/Phase/Interference/DedekindReciprocityLattice](DedekindReciprocityLattice.md)
