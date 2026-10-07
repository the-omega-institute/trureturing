# PrimeReflection

## Abstract

Prime-encoded polynomial evaluation and checked certificate chunks.

The function prime_eval interprets a monomial key by its prime factorization. The law prime_eval_nadd preserves evaluation under fuelled merge and coefficient collection. The function prime_encode maps sparse monomials to prime products.

The prime encoding and decoded tables use the definitions in SparseReflection. The first certificate block and the checks for chunks 12 through 17 and 19 through 47 live here. The checks for chunks 4 through 11 and 18, together with their data, live in SparseReflection. PrimeHierarchyCertificate assembles the chunk evaluation laws.

## References

- Dependency: [D5/S3/Quantum/Entanglement/HiguchiSudbery/SparseReflection](SparseReflection.md)
