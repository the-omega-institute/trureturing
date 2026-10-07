# PrimeHierarchyCertificate

## Abstract

Prime products encode monomials. The laws prime_eval_normalize and prime_eval_nadd preserve evaluation through the fuelled normalization and merge operations. The function prime_encode translates the sparse certificate data to this representation. The checked chunk and group identities yield prime_certificate_identity, the full mixed sum-of-squares identity used by the entropy bound.

The function prime_decodeTable in SparseReflection reads blocks of sixteen base-2^60 words. Each word stores the monomial key above its lowest 21 bits; those bits encode a signed coefficient as 2n for n and 2n+1 for -(n+1). The checks for chunks 4 through 11, 18, and 48 through 55 come from SparseReflection; the other early chunk checks come from PrimeReflection. The chunk and hierarchy checks compare the decoded tables with the computed polynomial operations.

## References

- Dependency: [D5/S3/Quantum/Entanglement/HiguchiSudbery/PrimeReflection](PrimeReflection.md)
