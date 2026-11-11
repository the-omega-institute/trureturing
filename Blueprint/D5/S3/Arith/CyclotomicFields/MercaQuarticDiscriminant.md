# The Actual Merca Quartic Discriminant

## Abstract

Actual maximal-order ramification, tame different and discriminant of the Merca cyclic quartic field.

For a prime r congruent to five modulo eight, lift maximal-order primes of the actual quartic fixed field to the ambient prime cyclotomic field. Unique total ramification upstairs and the inertia-degree tower give one prime downstairs with inertia degree one and ramification index four. The tame different has exact multiplicity three. Discriminant divisibility confines its support to r, and the CM signature fixes the positive sign.

**Theorem 1.1 (Actual ramification above r).**

Lean statement: `D5/S3/Arith/CyclotomicFields/MercaQuarticDiscriminant.prime_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CyclotomicFields/MercaQuarticDiscriminant.prime_structure` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

There is one actual maximal-order prime above r, with e=4 and f=1. The proof does not assume that two generates the full unit group.

**Theorem 1.2 (Actual different ideal).**

Lean statement: `D5/S3/Arith/CyclotomicFields/MercaQuarticDiscriminant.different_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CyclotomicFields/MercaQuarticDiscriminant.different_eq` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The genuine absolute different ideal is the cube of that prime. The lower different bound and the tame upper bound apply to the actual finite residue fields; r does not divide four.

**Theorem 1.3 (Genuine quartic field discriminant).**

Lean statement: `D5/S3/Arith/CyclotomicFields/MercaQuarticDiscriminant.discriminant`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CyclotomicFields/MercaQuarticDiscriminant.discriminant` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The actual number-field discriminant is r cubed. The norm of the different gives its absolute value and the two complex places give its positive sign.

This is a structural input to the relative ideal-class-number proof. It supplies no assumed class-number identity, signed quadratic L-value or complete MMZ criterion. Source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. No declared_validated status is claimed.

Historical statement: Haobo Ma and Wenlin Zhang, CC BY 4.0. Classical cyclotomic ramification and the existing Dedekind tame-different supplier are reused. Louboutin, Hudson and the classical class-number sources retain their attribution; no novelty or priority claim is made.

## References

- Truth anchor: `D5/S3/Arith/CyclotomicFields/MercaQuarticDiscriminant.different_eq`
- Truth anchor: `D5/S3/Arith/CyclotomicFields/MercaQuarticDiscriminant.discriminant`
- Truth anchor: `D5/S3/Arith/CyclotomicFields/MercaQuarticDiscriminant.prime_structure`
- Dependency: [D5/S3/Arith/CyclotomicFields/MercaQuadraticSubfield](MercaQuadraticSubfield.md)
- Dependency: [D5/S3/Factorization/Dedekind/TameDifferent](../../Factorization/Dedekind/TameDifferent.md)
