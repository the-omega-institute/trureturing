# Original parameter incidence and short vectors

## Abstract

Original integer parameter incidence for averaging the physical rational multiplicity. A short unit vector identifies the entire congruence lattice, so the count includes all actual slope lifts without an extra factor p.

Write Q(u,z)=(Y/X)u^2+(X/Y)z^2 and H^2=XY, with X,Y,H positive. The actual index-c lattice is c divides w*z-t*u, inside the literal integer rectangle |u|<=X, |z|<=Y. A ReducedMiddleBasis is an actual basis with its shortest-vector law and centered reduction. This module proves the geometric and congruence ingredients and their finite dyadic summation over the original integer parameters.

**Theorem 1.1 (Count the actual lattice section).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.actual_middle_box_section_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.actual_middle_box_section_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive c, any reduced actual basis B, and any finite set s of actual integer points of this lattice in the literal rectangle, card(s)<=16(1+H/sigma+XY/c), where sigma=sqrt(Q(B.R)). No counting injection is assumed.

Decompose each actual point in B. The proved coordinate square bounds imply |i|<=2H/sigma and |j|<=2H*sigma/c. Count the resulting integer rectangle and its image under the physical basis map. Reduction gives sigma^2<2c, absorbing the second boundary term into H/sigma. The remaining product term is exactly proportional to the physical area divided by the determinant.

**Theorem 1.2 (A unit vector fixes the actual lattice).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.middleLattice_eq_of_unit_vector`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.middleLattice_eq_of_unit_vector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If w and U.1 are units modulo c and the actual integer vector U lies in the lattice c divides w*z-t*u, then that lattice equals the lattice c divides U.1*z-U.2*u.

The original membership gives w*U.2=t*U.1 modulo c. Multiplying either determinant relation by the appropriate unit, applying this identity, and cancelling the unit proves both inclusions for actual integer vectors. There is no separate selection of a slope representative.

**Theorem 1.3 (Count original parameters incident to one shortest vector).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.original_short_vector_incidence_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.original_short_vector_incidence_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix nonzero c, positive X,Y,H with H^2=XY, and one nonzero actual integer vector U whose first coordinate is a unit modulo c. A finite set of original parameter vectors (w,t) in the literal rectangle, each with unit w, each containing U in its actual lattice and having U shortest, has cardinality at most 16(1+H/sqrt(Q(U))+XY/c).

The unit-vector identity makes all these actual lattices identical to the one determined by U. Choose an actual reduced basis for that lattice using the previously proved existence theorem. In the nonempty case the shortest-vector laws identify its squared first-vector length with Q(U). Antisymmetry of the integer determinant puts every original (w,t) into this fixed lattice; the actual box-section theorem counts these integer parameters directly. This already includes all full slopes arising from the original rectangle.

**Theorem 1.4 (Short vectors have two nonzero unit coordinates).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.short_middle_vector_unit_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.short_middle_vector_unit_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be prime, 0<X<=Y, Y<p^3 and XY<2p^4, and let t,w be units modulo p^2. Any nonzero actual vector U of their index-p^2 lattice with Q(U)<=XY/p^2 has both coordinates nonzero and both coordinates units modulo p^2.

An axis vector has its nonzero coordinate divisible by p^2. The norm bound and Y<p^3 exclude this. If both nonzero coordinates were divisible by p, then Q(U)>=2|U.1*U.2|>=2p^2, contradicting XY<2p^4. The original unit slope transfers divisibility by p between the coordinates, so neither coordinate is divisible by p. The prime-power unit criterion then gives both unit claims. The displayed cutoffs are explicit sufficient hypotheses, not silently inferred original-range assumptions.

**Theorem 1.5 (Count nonaxis short-vector candidates without a perimeter term).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.nonaxis_short_vector_candidates_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.nonaxis_short_vector_candidates_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive X,Y,H with H^2=XY and R>=0, every finite set of actual integer vectors with both coordinates nonzero and Q(U)<=R^2 has cardinality at most 4R^2.

The weighted ball lies in the anisotropic rectangle of half-widths RX/H and RY/H, whose product is R^2. Since both coordinates are nonzero, erase zero from each symmetric integer interval before multiplying the counts. Each remaining interval has at most twice its half-width, giving 4R^2 with no perimeter term.

**Theorem 1.6 (One actual shortest-vector scale).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.actual_shortest_vector_scale_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.actual_shortest_vector_scale_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Keep the prime, width and cutoff hypotheses above. For each original parameter wt in a finite set s in the literal box, choose the first vector U(wt) of an actual reduced index-p^2 basis. Suppose both original parameters are units modulo p^2 and R^2<=Q(U(wt))<=4R^2, with Q(U(wt))<=XY/p^2 and R>0. Then card(s)<=256R^2(1+H/R+XY/p^2).

Short-vector exclusion gives two unit coordinates for every candidate U. Count their actual image by the nonaxis ball bound at radius 2R, obtaining at most 16R^2 candidates. Partition the original integer parameters by their chosen vector. The proved original incidence count bounds each fiber by 16(1+H/sqrt(Q(U))+XY/p^2), at most 16(1+H/R+XY/p^2). Sum these actual fibers. The actual reduced bases supply all shortest-vector facts; no fiber-count supplier is assumed.

**Theorem 1.7 (Physical multiplicity of one shortest-vector scale).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.actual_shortest_vector_scale_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.actual_shortest_vector_scale_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the preceding actual scale hypotheses and R<=H/p, the sum over s of 1+H/(p*sqrt(Q(U(wt)))) is at most 512(H/p)(R+H+(XY/p^2)R).

The lower scale bound makes each physical weight at most 1+H/(pR), at most 2H/(pR) since R<=H/p. Multiply this bound by the proved actual scale count and simplify. The scale-independent term is (XY)/p, and the remaining terms are proportional to R, ready for the geometric summation.

**Theorem 1.8 (Average the actual physical rational multiplicity).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.actual_physical_weight_average`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.actual_physical_weight_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be prime, 1<=X<=Y, Y<p^3, XY<2p^4, H>0, H^2=XY and p<=H. For each original integer parameter wt in any finite set s in the literal rectangle, suppose both coordinates are units modulo p^2 and choose U(wt) as the first vector of an actual reduced index-p^2 basis. With A=XY, the sum of 1+H/(p*sqrt(Q(U(wt)))) is at most 2048[A+(A/p)(1+log(2p)/log(2))+A^2/p^4]. Existence of the required actual reduced bases was proved in PascadiOriginalLattice; no incidence count or parameter injection is supplied as a hypothesis.

Put T=H/p>=1 and choose an integer N with 2^N<=T<2^(N+1). Above norm T, each weight is at most 2 and the original rectangle contains at most 9A integer parameters, giving 18A. At smaller norms, the proved nonaxis exclusion gives length at least 1. Every actual shortest vector is therefore in a dyadic scale 2^k<=sigma<2^(k+1) with k<=N. A finite indicator-sum argument covers the original parameters by these actual scales without assuming a partition or injection.

Apply the proved physical scale bound at every k. The geometric sum of the scale lengths is at most 2T. The cutoff A<2p^4 gives T<2p, so the number of scales N+1 is at most 1+log(2p)/log(2). Summing gives 18A+1024A/p^2+512(A/p)(N+1)+1024A^2/p^4, which implies the displayed bound. Every candidate and incidence count concerns actual integer (w,t); there is no extra factor p from a freely selected slope lift.

Application boundary: the full physical-weight average is established under the stated explicit hypotheses for actual reduced bases. To apply it to the original prime-cube theorem one must check these width and size conditions in its parameter range and combine it with the original record counts, singular and exceptional charts, and exact reconstruction. The complete prime-cube six-tuple bound is not established by this module alone.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.actual_middle_box_section_count`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.actual_physical_weight_average`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.actual_shortest_vector_scale_count`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.actual_shortest_vector_scale_weight`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.middleLattice_eq_of_unit_vector`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.nonaxis_short_vector_candidates_count`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.original_short_vector_incidence_count`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage.short_middle_vector_unit_coordinates`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalLattice](PascadiOriginalLattice.md)
