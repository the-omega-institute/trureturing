# Multinomial moment matrices

## Abstract

Beta integrals and the Schur product establish positive semidefiniteness.

Nat denotes the nonnegative integers and Z the integers. Matrix.of is displayed with Fin-sized row and column binders and explicit val projections; det of the empty matrix is one. All floor quotients are natural division.

**Theorem 1.1 (Every nonnegative shift is positive semidefinite).**

$$\forall s \in Nat,\; \forall N \in Nat,\; PosSemidef\left((\operatorname{Matrix}.\operatorname{of}\left(\lambda (i: Fin\left(N\right)) \mapsto (\lambda (j: Fin\left(N\right)) \mapsto ((c\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + \operatorname{Fin}.\operatorname{val}\left(j\right) + s\right): Real)))\right): Matrix\left(Fin\left(N\right), Fin\left(N\right), Real\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hankel/SunA006077Positivity.multinomial_posSemidef` (`✓ std3`). ∎

*Citation.* K. A. Penson and A. I. Solomon (2001). *Coherent states from combinatorial sequences*. DOI: [10.48550/arXiv.quant-ph/0111151](https://doi.org/10.48550/arXiv.quant-ph/0111151). URL: <https://arxiv.org/abs/quant-ph/0111151v1>.

*Commentary.*

For 0<a<1 put mu(a,r)=(a)_r/r!. The normalized beta integral has these moments, and integrating t^s times a polynomial square gives a positive semidefinite matrix at every shift s. The identity c(r)=27^r mu(1/3,r) mu(2/3,r) follows from factorial recurrences. A Schur product, diagonal congruence by 27^i, and multiplication by 27^s give the stated matrix. Integrability follows from the beta integral with positive shifted shape. The cited note attests the positive-moment property of c; the beta construction here uses the existing real beta integral declarations.

## References

- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Positivity.multinomial_posSemidef`
- Dependency: [D5/S3/Analytic/KummerRatio/BetaIntegral](../../Analytic/KummerRatio/BetaIntegral.md)
- Dependency: [D5/S3/Combinatorics/Hankel/SunA006077](SunA006077.md)
