# Simultaneous tangent avoidance on common coverings

## Abstract

Simultaneous tangent avoidance on common coverings.

**Theorem 1.1 (One representative avoiding both tangent zeros).**

Lean statement: `D5/S3/Factorization/Mordell/TangentSignAvoidance.simultaneous_tangent_sign_avoidance`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/TangentSignAvoidance.simultaneous_tangent_sign_avoidance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be any characteristic-zero field, let q,r,a,b belong to K, suppose q*r is nonzero, 15*r is not 1, and a,b are not both zero. For every actual FieldKummer.CoveringRep c with d=q*r, b1=Units.mk0(q) and b2=1, there is another representative c' in that same covering type such that each coordinate of c' equals the corresponding coordinate of c or its negative, and both ((15*r+1)/2)*c'.z1+((15*r-1)/2)*c'.z3-15*r*c'.t and a*c'.z2-q*b*c'.z1-5*q*r*c'.t are nonzero. Both evaluations use this one c'. The construction actually keeps z1 unchanged.

The input is one nonzero tuple (t,z1,z2,z3). Its existing covering equations are z2 squared-q*z1 squared=5*q*r*t squared and q*z1 squared-q*z3 squared=15*q*r*t squared. Since q is nonzero, the second is equivalent to z1 squared-z3 squared=15*r*t squared. Conversely these two source equations make exactly an existing CoveringRep; adding them after multiplying the second by q gives z2 squared-q*z3 squared=20*q*r*t squared. Thus these are the three auxiliary conics for lambda=(q,1), with the product-normalized triple (q,1,q), imposed on one tuple.

For a nonzero x in characteristic zero, at least one of x+y and -x+y is nonzero: if both vanished their difference would be 2*x=0. If t is nonzero this chooses its sign to avoid the second tangent zero. If t=0 the equations and nonzeroness force z1 and z2 to be nonzero. When a is nonzero choose the sign of z2; when a=0, b is nonzero and the second tangent is already nonzero. These steps leave z1 unchanged.

If z3 is nonzero, its coefficient (15*r-1)/2 is nonzero, so choosing its sign avoids the first tangent zero without changing the second tangent. If z3=0, the second covering equation gives z1 squared=15*r*t squared and forces t nonzero. Vanishing of the first tangent would imply 15*r*(((15*r+1)/2) squared-15*r)*t squared=0. The middle factor equals (15*r-1) squared/4, contradicting the hypotheses. Changing coordinate signs preserves all squared equations and tuple nonzeroness.

Applying Quotient.mk to c' gives an actual FieldKummer.Covering(q*r,Units.mk0(q),1) point. The existing CommonRel quotient identifies common multiplication of all four coordinates by one nonzero field scalar. Independent coordinate signs need not be such a common scaling, so the resulting quotient point need not equal the input quotient point. No replacement quotient or separately chosen conic points are involved. The case t=0, root and two-torsion projections, and every permitted vanishing coordinate are included.

For theorem 79.1 take distinct natural primes q,r with q modulo 24 equal to 1, r modulo 24 equal to 19, and the three Legendre symbols (5/q)=(5/r)=(q/r)=1; put D=q*r. In the real field and in the p-adic field for any prime p, the natural casts give q*r nonzero and 15*r not equal to 1. Therefore the theorem transforms any supplied actual lambda covering representative over that field while retaining the full original hypotheses. The source tangent L2 subtracts ((1-15*r)/2)*z3; this is exactly addition of ((15*r-1)/2)*z3 here. L3 is exactly a*z2-q*b*z1-5*q*r*t. A norm witness a squared-q*b squared=5*q*r would imply that a,b are not both zero, but this theorem neither assumes nor constructs that norm witness.

This result is field algebra for an existing covering point. It supplies no rational norm existence or Hasse principle, rational affine normalization, local point existence or all-place assembly, integral or primitive local representatives, tangent valuation parity, Hilbert symbol factor, reciprocity or global scaling independence. It supplies no specified q-adic root or tangent-unit choice, including the exceptional 3*b+1=0 branch, and no Cassels pairing, quartic symbol, rank, generator, denominator, integrality or WSS conclusion.

## References

- Truth anchor: `D5/S3/Factorization/Mordell/TangentSignAvoidance.simultaneous_tangent_sign_avoidance`
- Dependency: [D5/S3/Factorization/Mordell/FieldKummer](FieldKummer.md)
