# Trace Detects Normal Elements for Galois p-Groups

## Abstract

The modular group algebra links a Galois orbit to its field trace.

**Theorem 1.1 (Independent conjugates exactly when trace is nonzero).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/PGroupNormalTrace.linearIndependent_conjugates_iff_trace_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/PGroupNormalTrace.linearIndependent_conjugates_iff_trace_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Webb (2016). *A Course in Finite Group Representation Theory*. DOI: [10.1017/CBO9781316677216](https://doi.org/10.1017/CBO9781316677216). URL: <https://www-users.cse.umn.edu/~webb/RepBook/RepBookLatex.pdf>.

*Commentary.*

For every finite Galois extension L/K in characteristic p whose full Galois group is a p-group, and every x in L, the family of all conjugates of x is K-linearly independent if and only if its field trace is nonzero. Since the Galois group has cardinality equal to the extension degree, this also says that the conjugates form a basis. The group need not be cyclic or abelian, and K need not be finite.

Use Mathlib's normal basis to identify K[G] linearly with L. In these coordinates, group multiplication agrees with the Galois action and trace is augmentation multiplied by the trace of the chosen normal element. Nonzero trace forces nonzero augmentation. The structural cardinal nilpotence theorem proves every element of the augmentation kernel nilpotent. The consumed Apache-2.0 unit criterion from Kitamura's AllPrimeGroups then makes the coordinate element a unit; right multiplication by it preserves independence. Conversely, a zero trace would give the nonzero all-ones linear relation between independent conjugates.

The unit criterion is reused from immutable revision 9253775c275153b1efb04f911b5c8740fed5a568 of KitaKen1/all-prime-residually-finite-p-groups, AllPrimeGroups/NilAugmentation.lean. Its source toolchain v4.34.1 differs from this repository's pin, so the consumed theorem is transplanted with its license and NOTICE. Its nilpotence hypothesis is discharged by the structural cardinal bound.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/PGroupNormalTrace.linearIndependent_conjugates_iff_trace_ne_zero`
- Dependency: [D5/S3/ArithUnits/MinacNguyenTanQuestion35](../../ArithUnits/MinacNguyenTanQuestion35.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/PGroupAugmentation](PGroupAugmentation.md)
