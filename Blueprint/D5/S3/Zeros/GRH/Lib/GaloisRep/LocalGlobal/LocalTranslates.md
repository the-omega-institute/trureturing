# Local Translates

## Abstract

Local Translates

Forms spherical off S; simultaneous diagonalisation of Hecke operators; levels off finite sets. Local component of a form: smooth, admissible, translates keep the Hecke eigensystem.

**Theorem 1.1 (hasHeckePolyAt_iff_localFormRep).**

Lean statement: `D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/LocalTranslates.hasHeckePolyAt_iff_localFormRep`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/LocalTranslates.hasHeckePolyAt_iff_localFormRep` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

At a split place w, a form x has Hecke polynomial P if and only if, in the local representation of GL_n(E_w) on forms, GL_n(O_w) fixes x, the j-th Hecke operator scales x by t_j, and P = Σ (−1)^j q_w^{j(j−1)/2} t_j X^{n−j}.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/LocalTranslates.hasHeckePolyAt_iff_localFormRep`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/FormRepresentation](../../Adelic/CuspForms/FormRepresentation.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/LocalGL/Iwahori/SortedExponents](../../LocalGL/Iwahori/SortedExponents.md)
