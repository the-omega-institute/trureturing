# Actual nonzero singular partners

## Abstract

The original nonzero singular stratum has a field-uniform subpower count of actual ordered integer endpoint pairs, with one physical fiber weight.

Fix a prime p and original units a1,a2,t,w modulo p^3. Let B be an actual oriented basis of the lattice p^3 divides w*z-t*u, and B2 a reduced actual basis of its index-p-squared counterpart. The anchor satisfies physical(B,q)=(-w,-t). Put Q(u,z)=(Y/X)u^2+(X/Y)z^2, H^2=XY and sigma=sqrt(Q(B2.R)), with X,Y,H positive. Both physical endpoints lie in the literal rectangle |u|<=X, |z|<=Y, with the separate widths 2X<p^3 and 2Y<p^3. Retain the original unit chart R.1, both baseline physical first coordinates and 1+a1*a2*t*w.

**Theorem 1.1 (Pass from genuine algebraic values to actual pairs).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalSingularCount.actual_singular_factor_partner_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalSingularCount.actual_singular_factor_partner_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For one relevant primitive factor F irreducible over the rationals, any finite set S of actual WordSolution endpoint pairs in that physical rectangle has at most card(valuePairs)*(1+6H/(p*sigma)) members whose integer pencil is divisible by F. The value-pair set is the actual image constructed in PascadiOriginalSingularPartners, and relevance means F vanishes at the genuine reduction of beta modulo p.

Equal algebraic values force F to divide the difference of the actual linear coordinate polynomials. When degree(F)>=2, the difference has degree at most one and must vanish; both actual coordinate vectors are therefore recovered uniquely from the value pair. A primitive relevant linear factor gives a fixed integer linear value. The existing physical fiber theorem counts its first actual endpoints by 1+6H/(p*sigma). The original word and physical width conditions make the second actual endpoint unique once the first is fixed. Thus the physical weight is paid once, including the degree-one case; no assumed observation injection replaces this reconstruction.

**Theorem 1.2 (Sum the actual nonzero singular stratum).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalSingularCount.actual_nonzero_singular_partners_subpower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalSingularCount.actual_nonzero_singular_partners_subpower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every epsilon>0, one C>0 is chosen before all original primes, parameters, bases, baseline and finite partner sets. Suppose 1<=J2<=J1; the anchor, baseline and all endpoint coordinates satisfy their J1,J2 bounds; the actual original word holds for the baseline and every partner; the retained unit and physical-box conditions above hold; every pencil is nonzero modulo p; and every pencil derivative vanishes at beta modulo p. If (J1*J2)^5<=M^5*p^3, (10368*3^9)^5*M^35<p^4 and (24*(8*18)^4)^5*M^40<p, then card(S)<=C*p^epsilon*(1+6H/(p*sigma)).

The preceding value-pair theorem constructs a cover of S by at most three genuine relevant primitive factors. Each factor has at most C0*p^epsilon actual value pairs, with the same constant chosen before its number field. Apply the actual factor-partner theorem to each member of that cover and sum the three bounds. The final constant is 3*C0. The cover, coordinate-to-value maps and physical fiber counts are all proved from the retained original endpoints. The auxiliary numerical height inequalities are derived within the supplier theorem from the stated cutoffs.

This is a count of actual ordered integer endpoint pairs in the specified nonzero singular stratum. It does not assume the cardinality of that stratum as an input, and it does not identify a value count with a point count. The modular-zero/content-p branch, excluded unit charts, actual parameter averaging, record summation, restoration of all original tuples and parameter cutoff handling remain separate obligations. In particular this result does not close the full Pascadi six-letter conjecture. The source problem and polynomial pencil are due to Pascadi; no worldwide priority or original-author acceptance claim is made.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalSingularCount.actual_nonzero_singular_partners_subpower`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalSingularCount.actual_singular_factor_partner_count`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers](PascadiOriginalLinearFibers.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalSingularPartners](PascadiOriginalSingularPartners.md)
