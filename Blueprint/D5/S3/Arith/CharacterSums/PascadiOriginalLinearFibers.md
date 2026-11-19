# Actual linear-factor fibers

## Abstract

Physical multiplicities for relevant primitive linear factors in the original prime-cube lattice. A factor direction gives a nonzero step pU with U in the index-p-squared congruence lattice. A fixed linear value has at most 1+6H/(p sigma) actual integer-coordinate preimages in the literal physical box.

Fix a prime p, positive X,Y,H with H^2=XY, an oriented basis B of the original lattice p^3 divides w*z-t*u, and a reduced basis B2 of the corresponding index-p^2 lattice with the same integer t,w. Put sigma=sqrt(Q(B2.R)) in the area-preserving weighted metric Q(u,z)=(Y/X)u^2+(X/Y)z^2. The reduced basis is an actual lattice basis with its shortest-vector law; no arbitrary slope lift or assumed counting injection is introduced. The earlier lattice existence theorem supplies this basis when w is a unit modulo p^2.

**Theorem 1.1 (A relevant direction descends to the p-squared lattice).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers.relevant_linear_physical_step`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers.relevant_linear_physical_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a,b be coprime integers and w a unit modulo p. If a*B.V.1+b*B.R.1 vanishes modulo p, then the nonzero physical step W=b*B.R+a*B.V equals pU for a nonzero integer vector U satisfying p^2 divides w*U.2-t*U.1.

The root condition makes W.1 divisible by p. Original lattice membership and the unit w force W.2 to be divisible by p as well. Dividing the original p^3 congruence by p gives the literal p^2 congruence for U. Coprimality and the determinant-p^3 basis rule out W=0.

**Theorem 1.2 (Actual physical preimages of a fixed linear value).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers.actual_linear_factor_fiber_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers.actual_linear_factor_fiber_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under those hypotheses, every finite set s of actual integer coordinate vectors z with physical B.R B.V z in the literal X by Y box and with a*z.1-b*z.2 equal to one fixed integer has cardinality at most 1+6H/(p*sigma). The constant is explicit and the shortest length is positive.

Bezout's identity expresses every coordinate difference in a fixed linear fiber as an integer multiple n of (b,a). Its physical difference is nW. The shortest-vector law and W=pU give Q(W)>=p^2*sigma^2, while two points in the original rectangle have squared distance at most 8XY. Thus |n|<=3H/(p*sigma). The actual coordinate map into these integer parameters is injective by the proved reconstruction identity. Counting the bounded integer interval gives the stated bound.

**Theorem 1.3 (The original word determines the second actual endpoint).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers.actual_first_endpoint_determines_second`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers.actual_first_endpoint_determines_second` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a nonzero modulus c, the original units a1,a2,t,w, the actual basis B of c divides w*z-t*u, and anchor coordinates q with physical B.R B.V q=(-w,-t). Retain the source unit 1-a1*a2*t*(physical q).1=1+a1*a2*t*w. Suppose two original WordSolution pairs have the same first actual coordinate vector x, while both second physical endpoints lie in the literal X by Y rectangle. Under the separate physical width conditions 2X<c and 2Y<c, their second coordinate vectors are equal. No injection or uniqueness supplier is an assumption.

Put g=a1*a2. The original six-return word supplies a+b+w=gtab. Consequently (1-gta)(1-gtb)=1+gtw. The retained right side is a unit, so 1-gta is a unit. Subtracting the two original equations and cancelling that unit fixes the second physical first coordinate modulo c. The bound 2X<c makes its two integer representatives equal. Membership in the original lattice and the unit w then fix the second physical coordinate modulo c; 2Y<c makes its integer representatives equal. Finally the determinant-c basis recovers the actual integer coordinate vector. The argument uses first-coordinate projection in the original physical box, with the lattice equation, rather than an assumed injection of a scalar on the full coordinate space.

**Theorem 1.4 (Pay the first physical fiber weight once).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers.actual_linear_factor_partner_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers.actual_linear_factor_partner_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Keep the prime-cube lattice, reduced index-p-squared basis, positive H with H^2=XY, primitive relevant linear factor and original units. Let s be any finite set of actual ordered coordinate pairs satisfying the original WordSolution, with both physical endpoints in the literal rectangle, and with a*e.1.1-b*e.1.2 equal to one fixed integer. Assume 2X<p^3 and 2Y<p^3 and retain the same unit right side. Then the number of actual pairs is at most 1+6H/(p*sigma), with exactly one physical fiber weight.

The preceding word-based uniqueness theorem proves that the first projection is injective on these actual pairs. The image consists of first points with the original fixed linear value and physical box condition. Reduce the original unit w from modulus p^3 to modulus p and apply the already proved actual_linear_factor_fiber_count to this image. Its cardinality equals the pair cardinality. No independent count of second-point fibers is multiplied into the estimate.

Application boundary: PascadiOriginalSingularCount connects equality of the constructed algebraic values for a primitive linear factor to the integer linear-value condition used here. This module proves word-based second-endpoint uniqueness and the single-weight actual ordered partner count under their stated unit and physical width assumptions. The average over original integer (t,w), excluded charts and full six-tuple count are not established by these fiber theorems alone.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers.actual_first_endpoint_determines_second`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers.actual_linear_factor_fiber_count`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers.actual_linear_factor_partner_count`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers.relevant_linear_physical_step`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalLattice](PascadiOriginalLattice.md)
