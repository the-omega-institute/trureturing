# Garcia--Volcic kernel rigidity

## Abstract

For every bounded self-adjoint tuple on a complex Hilbert space, the sharp Hunter residual has exactly the common kernel of the tuple.

**Definition 1.1 (Conjecture 4.5).**

$$claim \Leftrightarrow (\forall n:\mathbb{N}, \forall d:\mathbb{N}, (2 \le n) \Rightarrow ((2 \le d) \Rightarrow (\forall H:\operatorname{Type}, [\operatorname{NormedAddCommGroup}\left(H\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)] [\operatorname{CompleteSpace}\left(H\right)] \forall X:\operatorname{Fin}\left(n\right) \to \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right), (\forall i:\operatorname{Fin}\left(n\right), \operatorname{IsSelfAdjoint}\left(X\left(i\right)\right)) \Rightarrow (\operatorname{LinearMap.ker}\left(\operatorname{ContinuousLinearMap.toLinearMap}\left(\operatorname{residual}\left(n, d, X\right)\right)\right) = \operatorname{iInf}_{i:\operatorname{Fin}\left(n\right)} \operatorname{LinearMap.ker}\left(\operatorname{ContinuousLinearMap.toLinearMap}\left(X\left(i\right)\right)\right)))))$$

*Formalization.* `D5/S3/Analytic/Hunter/NCHunterKernelRigidity.claim` (`✓ std3`).

*Citation.* S. R. Garcia and J. Volčič (2025). *A noncommutative generalization of Hunter's positivity theorem*. DOI: [10.1090/proc/17480](https://doi.org/10.1090/proc/17480). URL: <https://arxiv.org/abs/2503.12376v2>.

*Commentary.*

Conjecture 4.5, page 11: “Let $n,d\geq2$. For all tuples of hermitian operators $X_{1}$,…,$X_{n}$ on a Hilbert space, ker ($H_{2d}$($X_{1}$,…,$X_{n}$) − $\mu_{n,d}$($X_{1}^{2d}$ + ⋯ + $X_{n}^{2d}$)) = ker $X_{1}$ ∩ ⋯ ∩ ker $X_{n}$.” Fin n indexes all n letters starting at zero. H is complete over C; ContinuousLinearMap represents bounded complex-linear operators. LinearMap.ker and iInf are the literal kernels and their intersection. H_{2d} is nchs n (2*d), using the reciprocal-fibre coefficient, and mu retains both parity branches and the n = 1 branch.

**Theorem 1.2 (The kernel equality).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hunter/NCHunterKernelRigidity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. R. Garcia and J. Volčič (2025). *A noncommutative generalization of Hunter's positivity theorem*. DOI: [10.1090/proc/17480](https://doi.org/10.1090/proc/17480). URL: <https://arxiv.org/abs/2503.12376v2>.

*Commentary.*

The positive residual form forces every mixed-word row to vanish. A strictly positive shifted factorial kernel then forces the grouped word coefficients to vanish. Even and odd degrees use separate contractions. Finally, a self-adjoint operator and its positive powers have the same kernel. The reverse inclusion follows by evaluating every positive-length word on the common kernel.

## References

- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterKernelRigidity.claim`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterKernelRigidity.result`
- Dependency: [D5/S3/Analytic/Hunter/NCHunterPositivity](NCHunterPositivity.md)
