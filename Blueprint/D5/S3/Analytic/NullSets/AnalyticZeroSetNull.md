# AnalyticZeroSetNull

## Abstract

A real analytic function on finite-dimensional real coordinate space has a null zero set whenever it has a nonzero value.

**Theorem 1.1 (ae_ne_zero_of_analytic).**

$$\forall (n : \mathbb{N}), \forall (f : \left(\operatorname{Fin}\left(n\right) \to \mathbb{R}\right) \to \mathbb{R}), \forall (a : \operatorname{Fin}\left(n\right) \to \mathbb{R}), (\operatorname{AnalyticOnNhd}\left(\mathbb{R}, f, \operatorname{Set.univ}\right) \land f\left(a\right) \ne 0) \Rightarrow \left(\forall^{\mathrm{m}}\right)_{(\operatorname{volume} : \operatorname{Measure}\left(\operatorname{Fin}\left(n\right) \to \mathbb{R}\right))} (x : \operatorname{Fin}\left(n\right) \to \mathbb{R}), f\left(x\right) \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NullSets/AnalyticZeroSetNull.ae_ne_zero_of_analytic` (`✓ std3`). ∎

*Citation.* B. S. Mityagin (2015). *The zero set of a real analytic function*. DOI: [10.48550/arXiv.1512.07276](https://doi.org/10.48550/arXiv.1512.07276). URL: <https://arxiv.org/abs/1512.07276v1>.

*Commentary.*

The one-dimensional identity theorem rules out a positive-measure zero set for a nontrivial analytic function. Induction on dimension applies this fact to sections, with Fubini and the measure-preserving decomposition of finite coordinate space. Polynomial evaluations and analytic circuit determinants are two applications.

## References

- Truth anchor: `D5/S3/Analytic/NullSets/AnalyticZeroSetNull.ae_ne_zero_of_analytic`
