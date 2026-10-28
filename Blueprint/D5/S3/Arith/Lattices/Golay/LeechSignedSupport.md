# Signed supports and parity reconstruction

## Abstract

Signed supports and parity reconstruction

Binary signs on a finite support give literal integer coordinates. Their sum, square sum and binary reduction retain the sign parity and the support. Deleting one coordinate gives a two-sided parametrization of even sign assignments. These elementary coordinate identities assert no lattice classification.

**Definition 1.1 (Literal signed coordinates).**

Lean statement: `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.signed`

*Formalization.* `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.signed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every integer k, finite support S among twenty-four positions, and binary sign function on S, signed k S assigns k times the corresponding sign on S and zero elsewhere. Signs are indexed by S itself, without an ordering.

**Theorem 1.2 (Square sum of a signed support).**

Lean statement: `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.signed_squareSum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.signed_squareSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer k, support S and sign assignment on S, squareSum of signed k S is k squared times the cardinality of S. Zero scale and empty support are included.

**Theorem 1.3 (Signs at a nonzero scale are recoverable).**

Lean statement: `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.signed_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.signed_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each nonzero integer k and support S, the map sending signs on S to signed k S is injective. Coordinate cancellation recovers every sign.

**Theorem 1.4 (Reconstruction from coordinate values).**

Lean statement: `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.exists_signed`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.exists_signed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any integer k, support S and integer vector x, if x is zero off S and equals k or minus k on S, some binary sign assignment on S reconstructs x exactly. The case k equal to zero is included.

**Theorem 1.5 (Binary reduction recovers the support word).**

Lean statement: `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.signed_two_red`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.signed_two_red` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every binary word c and every sign assignment on its nonzero support, dividing signed 2 (wordSupport c) coordinatewise by two and reducing modulo two recovers c, for both positive and negative signs.

**Definition 1.6 (One parity coordinate is determined).**

Lean statement: `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.evenSignsEquiv`

*Formalization.* `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.evenSignsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every support S and chosen element p of S, even binary sign assignments on S are equivalent to arbitrary assignments on the elements distinct from p. The missing bit is the sum of the others, so the total binary sum is zero.

**Theorem 1.7 (An octad has 128 even sign assignments).**

Lean statement: `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.evenSigns_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.evenSigns_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every support of cardinality eight has exactly 128 even sign assignments. Deleting one coordinate leaves seven independent binary choices.

**Theorem 1.8 (Integer divisibility implies binary parity).**

Lean statement: `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.evenSigns_of_sum_div_two`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.evenSigns_of_sum_div_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any support S and binary sign assignment, if the sum of lifted bits is divisible by two, the binary sum is zero. Together with the converse this converts the coordinate-sum congruence into the octad sign restriction.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.evenSignsEquiv`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.evenSigns_card`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.evenSigns_of_sum_div_two`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.exists_signed`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.signed`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.signed_injective`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.signed_squareSum`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/LeechSignedSupport.signed_two_red`
- Dependency: [D5/S3/Arith/Lattices/Golay/IntegerLeech](IntegerLeech.md)
