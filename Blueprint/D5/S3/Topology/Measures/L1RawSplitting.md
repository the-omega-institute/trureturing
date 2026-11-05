# Complete real L1 raw-restriction splitting

## Abstract

Complete real L1 raw-restriction splitting

**Theorem 1.1 (Complete real L1 raw-restriction splitting).**

Lean statement: `D5/S3/Topology/Measures/L1RawSplitting.exists_raw_restriction_splitting`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/L1RawSplitting.exists_raw_restriction_splitting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. Assume mu is finite, including zero. For every real L1 sequence f whose norms have a common real upper bound, there exist a strictly increasing natural selector j, actual measurable sets E(n) pairwise disjoint as sets, a real L1 vector v and a real r >= 0. Set u(n) to the literal restriction of f(j(n)) to E(n), and w(n) to its literal restriction to the complement. For each n, f(j(n)) = u(n) + w(n) exactly and norm(u(n)) + norm(w(n)) = norm(f(j(n))). For every continuous real linear functional phi on the entire L1 space, phi(w(n)) tends to phi(v). The norms of u(n) tend to r. No atomlessness, countable generation, ambient separability, nonzero measure, positivity or exact constant norm is assumed. The construction first concentrates the countable tail array, proves uniform integrability of the literal hard-tail complements, removes all later supports to obtain disjoint actual sets, and transfers genuine Banach-weak convergence across the resulting norm-null difference. It is classical subsequence splitting; it does not implement signed-measure transfer, the CH transfinite recursion or the full signed CH/Talagrand Problem 8.2.

## References

- Truth anchor: `D5/S3/Topology/Measures/L1RawSplitting.exists_raw_restriction_splitting`
- Dependency: [D5/S3/Topology/Measures/L1Biting](L1Biting.md)
- Dependency: [D5/S3/Topology/Measures/L1Disjointization](L1Disjointization.md)
- Dependency: [D5/S3/Topology/Measures/L1UniformIntegrableWeak](L1UniformIntegrableWeak.md)
