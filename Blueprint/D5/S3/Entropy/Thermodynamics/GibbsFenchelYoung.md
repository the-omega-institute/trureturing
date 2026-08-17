# The Finite Gibbs Fenchel-Young Identity

## Abstract

A finite Gibbs law satisfies the exact entropy-relative-entropy partition identity.

**Definition 1.1 (Finite Gibbs partition function).**

$$Z(H):=\sum_{i}\operatorname{exp}(H(i)).$$

*Formalization.* `D5/S3/Entropy/Thermodynamics/GibbsFenchelYoung.gibbsPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real energy profile H on a finite carrier, Z(H) is the sum of exp(H(i)). This sign convention matches the source identity log Tr exp(H), rather than the inverse-temperature convention exp(-H).

Every summand is strictly positive. On a nonempty carrier the partition function is therefore strictly positive, so its logarithm and the Gibbs normalization below have nonzero denominators.

**Definition 1.2 (Finite normalized Gibbs mass).**

$$g_{H}(i):=\frac{\operatorname{exp}(H(i))}{Z(H)}.$$

*Formalization.* `D5/S3/Entropy/Thermodynamics/GibbsFenchelYoung.gibbsMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Gibbs reference mass is exp(H(i)) divided by Z(H). The main theorem uses this definition pointwise as the second argument of the repository's existing finite real-valued KL divergence.

No second entropy or divergence is introduced. Shannon entropy remains the finite sum owned by MaxEntropy, and KL divergence remains the finite sum owned by ClassicalDPI.

**Theorem 1.3 (Finite Gibbs Fenchel-Young identity).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)] [\operatorname{Nonempty}(\iota)],\\\forall \rho, H: \iota\to \mathbb{R},\\((\forall i, 0< \rho(i)) \land \sum_{i}\rho(i)=1) \Rightarrow\\\log(Z(H))=\sum_{i}\rho(i)H(i)+S(\rho)+D(\rho\Vert g_{H}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Thermodynamics/GibbsFenchelYoung.finite_gibbs_fenchel_young` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be a strictly positive normalized mass function on a nonempty finite carrier. The logarithm of the Gibbs partition function equals the rho-expectation of H plus Shannon entropy S(rho) plus the finite KL divergence D(rho || g_H).

The proof expands each logarithmic ratio with Mathlib's Real.log_div, uses Real.log_exp for the Gibbs numerator, and then sums the pointwise identity. Normalization converts the remaining constant log Z(H) term into exactly one copy of log Z(H).

This closes only the finite classical diagonal form of the quantum Fenchel-Young clause in residual appendix E.161. It does not formalize matrix exponentials, density operators, symplectic duality, or the residual's decomposition and monotonicity claims.

Strict positivity of rho is an explicit scope restriction. Boundary probability laws with zero masses are not claimed here, even though a support-aware extension can be stated separately.

## References

- Truth anchor: `D5/S3/Entropy/Thermodynamics/GibbsFenchelYoung.finite_gibbs_fenchel_young`
- Truth anchor: `D5/S3/Entropy/Thermodynamics/GibbsFenchelYoung.gibbsMass`
- Truth anchor: `D5/S3/Entropy/Thermodynamics/GibbsFenchelYoung.gibbsPartition`
- Dependency: [D5/S3/Entropy/MaxEntropy](../MaxEntropy.md)
