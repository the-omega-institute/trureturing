# Group Base Change

## Abstract

Group Base Change

PEL datum with theta group, Lagrangian and padding; good primes; class identities. Base change of group schemes with ring action: points, sections, homomorphisms.

**Theorem 1.1 (exists_hom_baseChange).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Shimura/IntegralModel/GroupBaseChange.exists_hom_baseChange`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Shimura/IntegralModel/GroupBaseChange.exists_hom_baseChange` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let A', B' be base changes of A, B along b, c : S' → S, and F a natural map from c- to b-structures. An O-linear homomorphism χ : A → B induces one A' → B', acting on points through F and χ, compatible with pulled-back sections.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Shimura/IntegralModel/GroupBaseChange.exists_hom_baseChange`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/Adeles/AdditiveCharBasic](../../Adelic/Adeles/AdditiveCharBasic.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/AbelianScheme/KernelRing](../AbelianScheme/KernelRing.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/ThetaModuli/CutOutIdeals](../ThetaModuli/CutOutIdeals.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/Frames](../Uniformisation/Frames.md)
