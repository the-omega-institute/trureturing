# Unramified quadratic norms

## Abstract

Unramified quadratic norms and conic tangents.

**Theorem 1.1 (No cancellation in the quadratic norm).**

Lean statement: `D5/S3/Factorization/Mordell/UnramifiedQuadraticNorm.norm_size`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/UnramifiedQuadraticNorm.norm_size` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be prime and q a p-adic integer whose residue is not a square. For all p-adic numbers x and y, the norm of x squared minus q times y squared is the square of the larger of their norms. This is the quadratic-algebra norm with coefficients q and zero. There is no integrality restriction on x or y, and zero coordinates are included. Divide both coordinates by a nonzero coordinate of largest norm. Their reductions cannot have zero quadratic norm, since the residue quadratic algebra is a field. Its nonzero norm lifts to an integral unit; restoring the common scale gives the equality.

**Theorem 1.2 (A tangent norm identity).**

Lean statement: `D5/S3/Factorization/Mordell/UnramifiedQuadraticNorm.tangent_norm_size`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/UnramifiedQuadraticNorm.tangent_norm_size` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a squared minus q times b squared and x squared minus q times y squared both equal c, with 2c of norm one. Set ell equal to ax minus qby minus c and w equal to ay minus bx. Then the norm of ell equals the square of the maximum of the norms of ell and w. The identity ell squared minus q times w squared equals minus 2c times ell connects the same two conic points. Zero tangent evaluations remain included. For a nonzero tangent, the discrete p-adic norm formula identifies its valuation with twice the valuation of a coordinate attaining this maximum. The nonzero condition is essential when passing from norms to finite valuations.

**Theorem 1.3 (Common normalization and both tangent parities).**

Lean statement: `D5/S3/Factorization/Mordell/UnramifiedQuadraticNorm.common_tangent_parity`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/UnramifiedQuadraticNorm.common_tangent_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c and d be p-adic units and let 2 be a unit. Suppose a squared minus q times b squared is d. On one arbitrary nonzero homogeneous tuple (t,x,y,z), assume x squared minus q times y squared equals d times t squared and y squared minus z squared equals c times t squared. Then t is nonzero; a, b, x/t, y/t and z/t are integral. Both normalized tangents ((c+1)/2)(y/t)-((1-c)/2)(z/t)-c and a(x/t)-qb(y/t)-d are integral and every nonzero evaluation has even valuation. For an integral primitive tuple, t is a unit and the corresponding nonzero homogeneous evaluations also have even valuation. Primitivity means at least one of the four coordinate norms is one. All coordinates use the same scale t. No tangent nonvanishing or integral-input premise is imposed on the original tuple.

The nonsquare residue norm excludes t=0 and bounds the normalized x and y. The other equation bounds normalized z. For the split conic Y squared minus Z squared equals c, the product (Y+Z)(Y-Z)=c makes both factors units. Multiplying its tangent by 2(Y+Z) gives c(Y+Z-1) squared. The quadratic tangent uses the preceding norm identity. A primitive tuple and these common bounds force t to be a unit.

For the conditional rational norm witness in the quartic descent application, substitute c=15r, d=5qr, x=z2, y=z1 and z=z3. At a prime not dividing 30qr, c, d and 2 have norm one. The rational a and b embed into the same p-adic field; their integrality follows from the norm equation. This result does not construct the rational witness or assert any Hilbert-symbol, reciprocity, Selmer, Cassels-pairing, rank or all-place conclusion. Zero coordinates, a=0 and zero tangent evaluations are included; parity is asserted only for nonzero evaluations.

## References

- Truth anchor: `D5/S3/Factorization/Mordell/UnramifiedQuadraticNorm.common_tangent_parity`
- Truth anchor: `D5/S3/Factorization/Mordell/UnramifiedQuadraticNorm.norm_size`
- Truth anchor: `D5/S3/Factorization/Mordell/UnramifiedQuadraticNorm.tangent_norm_size`
