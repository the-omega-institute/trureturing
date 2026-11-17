# Algebraic values of actual singular partners

## Abstract

Original singular pencils construct genuine algebraic-integer value pairs with a field-uniform subpower count.

For an actual integer coordinate z=(i,j), write l_z(T)=i+jT. For an ordered endpoint e=(x,y) and anchor q, let L_e=l_x+l_y-l_q and Q_e=l_x*l_y. Relative to the retained baseline b, the original cubic pencil is P_e=L_b*Q_e-L_e*Q_b. The value polynomial is V_x=-Q_b+L_b*l_x, and the exact identity V_x*V_y-Q_b*(Q_b-L_b*l_q)=L_b*P_e connects the original endpoints to a fixed product. These are literal integer polynomials from Pascadi's six-return word, not independent coefficient records.

For a primitive factor F irreducible over the rationals, use the actual field K=AdjoinRoot(F), its root theta, and d=leadingCoeff(F). The algebraic integer d*theta gives the scaled quadratic value d^2*V_x(theta) in the actual ring of integers of K. The fixed product is d^4*Q_b(theta)*(Q_b-L_b*l_q)(theta). The first value and the product are constructed here; their integrality is proved rather than supplied as an assumption.

**Theorem 1.1 (The original word supplies the necessary units).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalSingularPartners.original_singular_unit_observations`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalSingularPartners.original_singular_unit_observations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonzero modulus c, retain units a1,a2, the first basis coordinate R.1, the negative second physical anchor coordinate t, both baseline physical first coordinates, and 1-a1*a2*t*(physical(q)).1. If the baseline satisfies the actual WordSolution, then L_b, Q_b and Q_b-L_b*l_q evaluated at beta=V.1/R.1 are all units modulo c.

The original endpoint identity gives alpha*L_b(beta)+Q_b(beta)=0 with alpha a unit. The two actual baseline first coordinates make Q_b(beta) a unit, hence L_b(beta) is a unit. Completing the original product identity using the retained unit right side gives the third unit. After reduction modulo p, these observations prevent a relevant factor from dividing any of the three polynomials over the rationals; in particular the constructed fixed product is nonzero.

**Theorem 1.2 (The genuine integer lift commutes with reduction).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalSingularPartners.reduce_eval_at_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalSingularPartners.reduce_eval_at_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a ring homomorphism f from ZMod c to ZMod p, an integer polynomial P, beta in ZMod c and an integer b satisfying b mod p=f(beta), reduction of P(beta) equals the integer P(b) reduced modulo p.

Polynomial evaluation commutes with the given ring homomorphism and with integer casting. This is the live bridge carrying the original unit observations to the integer lift used for the relevant factors.

**Theorem 1.3 (Equal algebraic values constrain actual integer coordinates).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalSingularPartners.singular_value_coordinate_divisibility`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalSingularPartners.singular_value_coordinate_divisibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose p is prime, F is primitive and irreducible over the rationals, F(b)=0 modulo p, and L_b(b) is a unit modulo p. If two actual coordinate vectors have the same constructed algebraic value, then F divides the difference of their integer linear coordinate polynomials.

The leading coefficient and L_b(theta) are nonzero. Cancel them from the equality of the actual scaled values. Evaluation at theta then kills the coordinate-polynomial difference. The AdjoinRoot kernel and primitive integer divisibility transfer this vanishing back to divisibility in the original integer polynomial ring.

**Theorem 1.4 (At most three relevant factors with uniformly few actual value pairs).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalSingularPartners.actual_singular_value_pairs_subpower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalSingularPartners.actual_singular_value_pairs_subpower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive epsilon, one positive constant C works before the choice of prime p, original chart, retained baseline and finite partner set S. Assume 1<=J2<=J1, coordinate bounds J1,J2 for the anchor, baseline and all endpoints, the actual WordSolution for the baseline and every partner, and the retained original unit conditions. Require every P_e to be nonzero modulo p and its derivative to vanish at beta modulo p. Under the explicit height cutoffs below, construct at most three primitive integer factors, each irreducible over the rationals of degree at most three and vanishing at the genuine lift modulo p. Every actual P_e is divisible by one of these factors. For each factor the finite image of actual algebraic value pairs has cardinality at most C*p^epsilon.

Choose one actual partner in the nonempty case and factor its actual cubic pencil. The original root and singularity conditions, coefficient bounds and resultant estimates cover every partner by at most three relevant factors. Their coefficients and Cauchy root bounds give an upper bound p^18 at every complex embedding of the constructed first value. The nonzero constructed product has absolute integral norm at most p^108. Apply NumberFieldDivisorSubpower.fixed_product_pairs_subpower with its constant already uniform over all fields of degree at most three. No field-dependent regulator or class-number constant enters.

The height cutoffs are (J1*J2)^5<=M^5*p^3, (10368*3^9)^5*M^35<p^4 and (24*(8*18)^4)^5*M^40<p. The auxiliary inequalities p>=16 and 18*J1^3<=p^2 are derived from these original inputs, not added hypotheses.

This module counts actual algebraic value pairs. The following PascadiOriginalSingularCount module proves the fibers back to actual integer endpoint pairs and sums the at most three factors with one physical linear-fiber weight. The modular-zero/content-p stratum, exceptional charts, averaging and full six-tuple bound are not proved by this value count alone. The original conjecture remains open here. The polynomial/divisor strategy and source counting problem are attributed to Pascadi; the uniform divisor ingredients use classical number-field arithmetic.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalSingularPartners.actual_singular_value_pairs_subpower`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalSingularPartners.original_singular_unit_observations`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalSingularPartners.reduce_eval_at_lift`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalSingularPartners.singular_value_coordinate_divisibility`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalCoefficients](PascadiOriginalCoefficients.md)
- Dependency: [D5/S3/Arith/Divisors/NumberFieldDivisorSubpower](../Divisors/NumberFieldDivisorSubpower.md)
