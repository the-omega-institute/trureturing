# GeneralizedPseudostandardPeriodicity

## Abstract

Generalized pseudostandard words and involutory reflection structure.

**Definition 1.1 (TailConditions).**

$$\forall (alpha : Type) (delta : \mathbb{N} \to alpha) (Theta : \mathbb{N} \to InvAntimorphism alpha) (k : \mathbb{N}) , TailConditions delta Theta k \iff (\forall (i j : \mathbb{N}) , 1 \leq i \to 1 \leq j \to (Theta (k + i)) . toFun [delta (k + i + 1)] = (Theta (k + j)) . toFun [delta (k + j + 1)]) \land (\forall (i : \mathbb{N}) , 1 \leq i \to \forall (w : List alpha) , (Theta (k + i)) . toFun w = w \to (Theta (k + i + 2)) . toFun ((Theta (k + i + 1)) . toFun w) = (Theta (k + i + 1)) . toFun w)$$

*Formalization.* `D5/S1/Words/Palindromes/GeneralizedPseudostandardPeriodicity.TailConditions` (`✓ std3`).

*Citation.* J. Florian, Ľ. Dvořáková (2016). *On periodicity of generalized pseudostandard words*. DOI: [10.37236/4771](https://doi.org/10.37236/4771). URL: <https://arxiv.org/abs/1508.02020>.

*Commentary.*

ArXiv v1, pages 20–21, Conjecture 29: Consider an alphabet 𝒜 with #𝒜=d and G the set of all involutory antimorphisms on 𝒜^*. Let 𝐮(Δ, Θ) be a d-ary generalized pseudostandard word, where Δ is a sequence of letters from 𝒜 and Θ is a sequence of antimorphisms from G. Then 𝐮 is periodic if and only if the following conditions are met: 1. The normalized directive bi-sequence is of the form (Δ̃, Θ̃)=(vδ₁δ₂δ₃…, σ ϑ₁ ϑ₂ϑ₃…), where |v|=|σ| and ϑᵢ(δᵢ₊₁)=ϑⱼ(δⱼ₊₁) for all i,j ∈ ℕ. 2. For all i ∈ ℕ, if w is a ϑᵢ-palindrome, then ϑᵢ₊₁(w) is a ϑᵢ₊₂-palindrome. The tail begins after k entries. Both tail indices start at one; images of letters are one-letter words.

**Definition 1.2 (claim).**

$$claim \iff \forall (alpha : Type) [Fintype alpha] [DecidableEq alpha] , (\forall (delta : \mathbb{N} \to alpha) (Theta : \mathbb{N} \to InvAntimorphism alpha) (u : \mathbb{N} \to alpha) (W : \mathbb{N} \to List alpha) , Generates delta Theta u W \to \exists (deltap : \mathbb{N} \to alpha) (Thetap : \mathbb{N} \to InvAntimorphism alpha) (Wp : \mathbb{N} \to List alpha) , Generates deltap Thetap u Wp \land IsNormalized u Wp) \land (\forall (delta : \mathbb{N} \to alpha) (Theta : \mathbb{N} \to InvAntimorphism alpha) (u : \mathbb{N} \to alpha) (W : \mathbb{N} \to List alpha) , Generates delta Theta u W \to IsNormalized u W \to Function.\operatorname{Surjective} u \to ((\exists (p : \mathbb{N}) , 0 < p \land Function.\operatorname{Periodic} u p) \iff \exists (k : \mathbb{N}) , TailConditions delta Theta k))$$

*Formalization.* `D5/S1/Words/Palindromes/GeneralizedPseudostandardPeriodicity.claim` (`✓ std3`).

*Citation.* J. Florian, Ľ. Dvořáková (2016). *On periodicity of generalized pseudostandard words*. DOI: [10.37236/4771](https://doi.org/10.37236/4771). URL: <https://arxiv.org/abs/1508.02020>.

*Commentary.*

ArXiv v1, pages 20–21, Conjecture 29: Consider an alphabet 𝒜 with #𝒜=d and G the set of all involutory antimorphisms on 𝒜^*. Let 𝐮(Δ, Θ) be a d-ary generalized pseudostandard word, where Δ is a sequence of letters from 𝒜 and Θ is a sequence of antimorphisms from G. Then 𝐮 is periodic if and only if the following conditions are met: 1. The normalized directive bi-sequence is of the form (Δ̃, Θ̃)=(vδ₁δ₂δ₃…, σ ϑ₁ ϑ₂ϑ₃…), where |v|=|σ| and ϑᵢ(δᵢ₊₁)=ϑⱼ(δⱼ₊₁) for all i,j ∈ ℕ. 2. For all i ∈ ℕ, if w is a ϑᵢ-palindrome, then ϑᵢ₊₁(w) is a ϑᵢ₊₂-palindrome. The alphabet is any finite type. Surjectivity says that every letter occurs. Periods are positive natural numbers and are pure periods. The first conjunct also gives a normalized directive for each generated word.

**Theorem 1.3 (result).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/GeneralizedPseudostandardPeriodicity.result` (`✓ std3`). ∎

*Resolves.* `Problems/florian-dvorakova-2016-generalized-pseudostandard-periodicity` (proved) by `D5/S1/Words/Palindromes/GeneralizedPseudostandardPeriodicity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"florian-dvorakova-2016-generalized-pseudostandard-periodicity","declaration_gid":"D5/S1/Words/Palindromes/GeneralizedPseudostandardPeriodicity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* J. Florian, Ľ. Dvořáková (2016). *On periodicity of generalized pseudostandard words*. DOI: [10.37236/4771](https://doi.org/10.37236/4771). URL: <https://arxiv.org/abs/1508.02020>.

*Commentary.*

Every finite alphabet admits normalization, and a normalized directive of a word using every letter satisfies the two tail conditions exactly when the word has a positive pure period.

## References

- Truth anchor: `D5/S1/Words/Palindromes/GeneralizedPseudostandardPeriodicity.TailConditions`
- Truth anchor: `D5/S1/Words/Palindromes/GeneralizedPseudostandardPeriodicity.claim`
- Truth anchor: `D5/S1/Words/Palindromes/GeneralizedPseudostandardPeriodicity.result`
- Dependency: [D5/S1/Words/Palindromes/PseudopalindromicNormalization](PseudopalindromicNormalization.md)
