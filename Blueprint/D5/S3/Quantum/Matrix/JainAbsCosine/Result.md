# Multiplicity from Fourier mode separation

## Abstract

Exactly double nonzero eigenvalues for the odd absolute cosine power matrix.

**Theorem 1.1 (The nonzero multiplicity conjecture).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JainAbsCosine/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/jain-2017-abs-cosine-hadamard-power-multiplicity-two` (proved) by `D5/S3/Quantum/Matrix/JainAbsCosine/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"jain-2017-abs-cosine-hadamard-power-multiplicity-two","declaration_gid":"D5/S3/Quantum/Matrix/JainAbsCosine/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Tanvi Jain (2017). *Hadamard powers of some positive matrices*. DOI: [10.1016/j.laa.2016.06.030](https://doi.org/10.1016/j.laa.2016.06.030). URL: <https://doi.org/10.1016/j.laa.2016.06.030>.

*Commentary.*

For every odd order 2m+1 with m at least one and every nonnegative real exponent, every nonzero characteristic root other than the largest Fourier mode has algebraic multiplicity exactly two. The matrix and the claim are those of Jain. Periodicity of the absolute cosine identifies the matrix as a real circulant. Reflection pairs its Fourier factors into one linear factor for the constant mode and squared linear factors for the remaining modes. The exact gap signs separate all nonzero representative values. Removing the unique squared factor leaves a polynomial that does not vanish at the chosen root, so the root multiplicity is exactly two.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/Result.result`
- Dependency: [D5/S3/Quantum/Matrix/CirculantCharpoly](../CirculantCharpoly.md)
- Dependency: [D5/S3/Quantum/Matrix/JainAbsCosine/Separation](Separation.md)
