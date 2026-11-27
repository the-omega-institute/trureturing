# Appell Humbert

## Abstract

Appell Humbert

complex uniformisation of PEL abelian varieties, Appell–Humbert and finite class number. Here the signature is (1,n-1) at one place and definite elsewhere. The torus comes from the exponential of a compact commutative complex Lie group, and Appell–Humbert is proved only for a very ample class obeying the parallelogram law. Source: J. S. Milne, Introduction to Shimura Varieties (2005/2017), Theorem 8.17 and Lemma 5.12; R. Kottwitz, Points on some Shimura varieties over finite fields, J. AMS 5 (1992) §8; G. Shimura, On analytic families of polarized abelian varieties and automorphic functions, Ann. Math. 78 (1963); A. Borel, Some finiteness properties of adele groups over number fields, Publ. IHES 16 (1963); D. Mumford, Abelian Varieties §§1–2; L. Breen, Fonctions thêta et théorème du cube, LNM 980 (1983).

**Theorem 1.1 (appell_humbert).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/AppellHumbert.appell_humbert`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/AppellHumbert.appell_humbert` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Appell–Humbert theorem: if V/L ≅ A(ℂ) is a uniformisation and N a projective embedding of A whose class is symmetric and satisfies the parallelogram law Pic.ParallelogramLaw, the coordinates of N are theta functions for L of some type (B, χ) with positive Riemann form.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/AppellHumbert.appell_humbert`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Geometry/SerreSaturation](../../General/Geometry/SerreSaturation.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/AbelianScheme/ThetaFamily](../AbelianScheme/ThetaFamily.md)
