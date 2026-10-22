# The two parameter thresholds

## Abstract

Sharp zero-balanced Gauss quotient classifications

**Theorem 1.1 (The two classifications).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/qiu-ma-xiang-2024-zero-balanced-gauss-turan` (proved) by `D5/S3/Analytic/GaussZeroBalanced/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"qiu-ma-xiang-2024-zero-balanced-gauss-turan","declaration_gid":"D5/S3/Analytic/GaussZeroBalanced/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* S.-L. Qiu, X.-Y. Ma and X.-Y. Xiang (2024). *Turán-type inequalities for Gaussian hypergeometric functions, and Baricz's conjecture*. DOI: [10.48550/arXiv.2408.15723](https://doi.org/10.48550/arXiv.2408.15723). URL: <https://arxiv.org/abs/2408.15723>.

*Commentary.*

For every positive real a and b, the derivative in b of quot a b x is strictly negative for every x in (0,1) if and only if b<=sqrt(a(a+1)). For every real a in (0,1), ineq17 a r holds for every r in (0,1) if and only if a>=3/7.

The first classification follows from the parameter variational equation, the strict Riccati certificate and the initial mixed derivative. For the second classification, the difference w=f(a,b1)-f(a,b2), with 0<b1<b2, satisfies x w prime+P w=(b2-b1)(a squared t f(a,b1) squared/((a+b1)(a+b2))-(1-f(a,b1))), where P=a+b2+ab2 t(f(a,b1)+f(a,b2))/(a+b2) and t=x/(1-x). The certificate makes the source strictly positive when b1 b2<=a(a+1). The singular endpoint comparison yields w>0. Conversely, w>0 on the interval forces its initial slope to be nonnegative, hence b1 b2<=a(a+1). Substitution b1=1-a and b2=3/2-a gives a(a+1)-b1 b2=(7a-3)/2, so the threshold is exactly 3/7.

## References

- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Result.result`
- Dependency: [D5/S3/Analytic/GaussZeroBalanced/Comparison](Comparison.md)
- Dependency: [D5/S3/Analytic/GaussZeroBalanced/ParamDeriv](ParamDeriv.md)
