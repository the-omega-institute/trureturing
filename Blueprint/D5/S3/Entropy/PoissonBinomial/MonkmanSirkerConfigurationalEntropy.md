# Monkman–Sirker Configurational Entropy

## Abstract

Poisson-binomial configurational entropy is nondecreasing under majorization throughout the closed unit cube.

**Definition 1.1 (The majorization claim).**

$$\forall M: \mathbb{N}, \forall c: \operatorname{Fin}\left(M\right) \to \mathbb{R}, \forall d: \operatorname{Fin}\left(M\right) \to \mathbb{R}, (\forall i: \operatorname{Fin}\left(M\right), 0\le\operatorname{c}\left(i\right)\land \operatorname{c}\left(i\right)\le1) \Rightarrow (\forall i: \operatorname{Fin}\left(M\right), 0\le\operatorname{d}\left(i\right)\land \operatorname{d}\left(i\right)\le1) \Rightarrow \operatorname{moreMixed}\left(d, c\right) \Rightarrow \operatorname{F}\left(c\right)\le\operatorname{F}\left(d\right)$$

*Formalization.* `D5/S3/Entropy/PoissonBinomial/MonkmanSirkerConfigurationalEntropy.claim` (`✓ std3`).

*Citation.* D. Monkman; J. Sirker (2023). *Symmetry-resolved entanglement: general considerations, calculation from correlation functions, and bounds for symmetry-protected topological phases*. DOI: [10.48550/arXiv.2307.05820](https://doi.org/10.48550/arXiv.2307.05820). URL: <https://arxiv.org/abs/2307.05820>.

*Commentary.*

Monkman and Sirker, Section 3.3, ‘A conjecture on the concavity of Sc’: "We note that the configurational entropy Sc = S + (−SN) is a sum of a concave and a convex function. Therefore, one cannot directly apply majorization to Sc based on the already obtained results for S and SN. However, this does not rule our that Sc is also a concave function of the parameters {Ck}. Similar to the original Shepp-Olkin paper [22] we will here just investigate the cases M = 2 and M = 3. Based on these results, we conjecture that Sc({Ck}) is indeed Schur concave and majorization thus applies."

For every finite dimension M and two vectors c and d in the closed unit cube, moreMixed d c implies F c at most F d. Here F is the sum of binary entropies minus the entropy of the sum of the independent Bernoulli variables; logarithms are natural.

**Theorem 1.2 (Majorization increases configurational entropy).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/PoissonBinomial/MonkmanSirkerConfigurationalEntropy.result` (`✓ std3`). ∎

*Resolves.* `Problems/monkman-sirker-2023-configurational-entropy-schur-concavity` (proved) by `D5/S3/Entropy/PoissonBinomial/MonkmanSirkerConfigurationalEntropy.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"monkman-sirker-2023-configurational-entropy-schur-concavity","declaration_gid":"D5/S3/Entropy/PoissonBinomial/MonkmanSirkerConfigurationalEntropy.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. Monkman; J. Sirker (2023). *Symmetry-resolved entanglement: general considerations, calculation from correlation functions, and bounds for symmetry-protected topological phases*. DOI: [10.48550/arXiv.2307.05820](https://doi.org/10.48550/arXiv.2307.05820). URL: <https://arxiv.org/abs/2307.05820>.

*Commentary.*

The interior majorization chain reduces the assertion to the pairwise T-transform inequality. For boundary vectors, the same increasing affine map sends both vectors to the open cube and preserves the descending-prefix majorization inequalities. Continuity passes the inequality to the original vectors.

This statement includes empty vectors and deterministic Bernoulli parameters. It does not assert joint concavity, strict Schur concavity or classify equality cases. The proof uses general finite-dimensional inequalities rather than bounded enumeration or numerical certification.

## References

- Truth anchor: `D5/S3/Entropy/PoissonBinomial/MonkmanSirkerConfigurationalEntropy.claim`
- Truth anchor: `D5/S3/Entropy/PoissonBinomial/MonkmanSirkerConfigurationalEntropy.result`
- Dependency: [D5/S3/Entropy/PoissonBinomial/ConfigurationalEntropyStep](ConfigurationalEntropyStep.md)
