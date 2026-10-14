# PseudopalindromicNormalization

## Abstract

Generalized pseudostandard words and involutory reflection structure.

**Definition 1.1 (InvAntimorphism).**

$$\forall (alpha : Type) , InvAntimorphism alpha := ((toFun : List alpha \to List alpha) , (\forall (v w : List alpha) , toFun (v ++ w) = toFun w ++ toFun v) , (\forall (w : List alpha) , toFun (toFun w) = w))$$

*Formalization.* `D5/S1/Words/Palindromes/PseudopalindromicNormalization.InvAntimorphism` (`✓ std3`).

*Citation.* J. Florian, Ľ. Dvořáková (2016). *On periodicity of generalized pseudostandard words*. DOI: [10.37236/4771](https://doi.org/10.37236/4771). URL: <https://arxiv.org/abs/1508.02020>.

*Commentary.*

ArXiv v1, page 3: “An involutory antimorphism is a map ϑ : A* → A* such that for every v,w ∈ A* we have ϑ(vw) = ϑ(w)ϑ(v) and moreover ϑ² equals identity.” The structure has a word map toFun and proofs of the two displayed laws. The record notation lists precisely those data and laws.

**Theorem 1.2 (InvAntimorphism.singletonExists).**

$$\forall (alpha : Type) (theta : InvAntimorphism alpha) (a : alpha) , \exists (b : alpha) , theta.\operatorname{toFun} [a] = [b]$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.singletonExists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The image of a one-letter word is a one-letter word.

**Definition 1.3 (InvAntimorphism.letter).**

$$\forall (alpha : Type) (theta : InvAntimorphism alpha) (a : alpha) , theta.\operatorname{letter} a = Classical.\operatorname{choose} (InvAntimorphism.\operatorname{singletonExists} theta a)$$

*Formalization.* `D5/S1/Words/Palindromes/PseudopalindromicNormalization.letter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image of a one-letter word has exactly one letter; Classical.choose selects that letter.

**Theorem 1.4 (InvAntimorphism.map_singleton).**

$$\forall (alpha : Type) (theta : InvAntimorphism alpha) (a : alpha) , theta.\operatorname{toFun} [a] = [theta.\operatorname{letter} a]$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.map_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected letter is exactly the image of the input letter.

**Theorem 1.5 (InvAntimorphism.letterInvolutive).**

$$\forall (alpha : Type) (theta : InvAntimorphism alpha) (a : alpha) , theta.\operatorname{letter} (theta.\operatorname{letter} a) = a$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.letterInvolutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The action on letters is involutive.

**Definition 1.6 (InvAntimorphism.perm).**

$$\forall (alpha : Type) (theta : InvAntimorphism alpha) , theta.\operatorname{perm} = Function.\operatorname{Involutive}.\operatorname{toPerm} theta.\operatorname{letter} (InvAntimorphism.\operatorname{letterInvolutive} theta)$$

*Formalization.* `D5/S1/Words/Palindromes/PseudopalindromicNormalization.perm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib converts the involutive letter map to an equivalence of the alphabet.

**Theorem 1.7 (InvAntimorphism.perm_apply).**

$$\forall (alpha : Type) (theta : InvAntimorphism alpha) (a : alpha) , theta.\operatorname{perm} a = theta.\operatorname{letter} a$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.perm_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The letter permutation acts by the selected letter map.

**Theorem 1.8 (InvAntimorphism.perm_unique).**

$$\forall (alpha : Type) (theta : InvAntimorphism alpha) (pi : Equiv.\operatorname{Perm} alpha) , (\forall (w : List alpha) , theta.\operatorname{toFun} w = (List.\operatorname{map} (DFunLike.\operatorname{coe} pi) w) . reverse) \to pi = theta.\operatorname{perm}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.perm_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reversed-letter representation determines its letter permutation uniquely.

**Theorem 1.9 (InvAntimorphism.map_word).**

$$\forall (alpha : Type) (theta : InvAntimorphism alpha) (w : List alpha) , theta.\operatorname{toFun} w = (List.\operatorname{map} (DFunLike.\operatorname{coe} theta.\operatorname{perm}) w) . reverse$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.map_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the letter permutation to the word and reverse the result.

**Theorem 1.10 (palindrome_transport_iff).**

$$\forall (alpha : Type) (theta sigma tau : InvAntimorphism alpha) , (\forall (w : List alpha) , Function.\operatorname{IsFixedPt} theta.\operatorname{toFun} w \to Function.\operatorname{IsFixedPt} tau.\operatorname{toFun} (sigma.\operatorname{toFun} w)) \iff tau.\operatorname{perm} = sigma.\operatorname{perm} \cdot theta.\operatorname{perm} \cdot sigma.\operatorname{perm}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.palindrome_transport_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport of all fixed words is equivalent to conjugation of the involutive letter permutations. Two-letter fixed words determine the converse.

**Theorem 1.11 (InvAntimorphism.prefix_to_suffix).**

$$\forall (alpha : Type) (sigma : InvAntimorphism alpha) (P Q : List alpha) , P <+: Q \to Function.\operatorname{IsFixedPt} sigma.\operatorname{toFun} Q \to sigma.\operatorname{toFun} P <:+ Q$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.prefix_to_suffix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The antimorphic image of a prefix is a suffix of any fixed extension.

**Definition 1.12 (IsClosure).**

$$\forall (alpha : Type) (theta : InvAntimorphism alpha) (w z : List alpha) , IsClosure theta w z \iff List.\operatorname{IsPrefix} w z \land theta.\operatorname{toFun} z = z \land (\forall (v : List alpha) , List.\operatorname{IsPrefix} w v \to theta.\operatorname{toFun} v = v \to z.\operatorname{length} \leq v.\operatorname{length})$$

*Formalization.* `D5/S1/Words/Palindromes/PseudopalindromicNormalization.IsClosure` (`✓ std3`).

*Citation.* J. Florian, Ľ. Dvořáková (2016). *On periodicity of generalized pseudostandard words*. DOI: [10.37236/4771](https://doi.org/10.37236/4771). URL: <https://arxiv.org/abs/1508.02020>.

*Commentary.*

ArXiv v1, page 3: “The ϑ-palindromic closure wϑ of a word w is the shortest ϑ-palindrome having w as prefix.” The final universal inequality expresses shortest length among all such extensions.

**Definition 1.13 (Generates).**

$$\forall (alpha : Type) (delta : \mathbb{N} \to alpha) (Theta : \mathbb{N} \to InvAntimorphism alpha) (u : \mathbb{N} \to alpha) (W : \mathbb{N} \to List alpha) , Generates delta Theta u W \iff W 0 = [] \land (\forall (n : \mathbb{N}) , IsClosure (Theta (n + 1)) (W n ++ [delta (n + 1)]) (W (n + 1))) \land (\forall (n : \mathbb{N}) , W n = List.\operatorname{ofFn} (fun (i : Fin ((W n) . length)) \mapsto u \operatorname{val}\left(i\right)))$$

*Formalization.* `D5/S1/Words/Palindromes/PseudopalindromicNormalization.Generates` (`✓ std3`).

*Citation.* J. Florian, Ľ. Dvořáková (2016). *On periodicity of generalized pseudostandard words*. DOI: [10.37236/4771](https://doi.org/10.37236/4771). URL: <https://arxiv.org/abs/1508.02020>.

*Commentary.*

“Let 𝒜 be an alphabet and G be the set of all involutory antimorphisms on 𝒜^*. Let Δ=δ₁δ₂… and Θ=ϑ₁ϑ₂…, where δᵢ∈𝒜 and ϑᵢ∈ G for all i∈ℕ. The infinite generalized pseudostandard word 𝐮(Δ,Θ) generated by the generalized pseudopalindromic closure is the word whose prefixes wₙ are obtained from the recurrence relation wₙ₊₁=(wₙδₙ₊₁)^ϑₙ₊₁,  w₀=ε. The sequence Λ=(Δ,Θ) is called the directive bi-sequence of the word 𝐮(Δ,Θ).” Infinite prefixes are the displayed List.ofFn expressions. Directive entries at zero are unused.

**Theorem 1.14 (pal_wrap).**

$$\forall (alpha : Type) (theta : InvAntimorphism alpha) (p s : List alpha) , Function.\operatorname{IsFixedPt} theta.\operatorname{toFun} s \to Function.\operatorname{IsFixedPt} theta.\operatorname{toFun} (p ++ s ++ theta.\operatorname{toFun} p)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.pal_wrap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Wrapping a fixed word by a word and its antimorphic image gives a fixed word.

**Theorem 1.15 (closure_suffix_bound).**

$$\forall (alpha : Type) (theta : InvAntimorphism alpha) (w z s : List alpha) , IsClosure theta w z \to s <:+ w \to Function.\operatorname{IsFixedPt} theta.\operatorname{toFun} s \to z.\operatorname{length} + s.\operatorname{length} \leq 2 \cdot w.\operatorname{length}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.closure_suffix_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fixed suffix bounds the extra length needed for closure.

**Theorem 1.16 (finite_border_period).**

$$\forall (alpha : Type) (P Q : List alpha) , P <+: Q \to P <:+ Q \to \forall (d : \mathbb{N}) , P . length + d = Q . length \to \forall (j : \mathbb{N}) , j + d < Q . length \to Q [j + d] = Q [j]$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.finite_border_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A prefix and suffix with a fixed length offset impose the corresponding period on every valid position.

**Theorem 1.17 (pre_length).**

$$\forall (alpha : Type) (u : \mathbb{N} \to alpha) (m : \mathbb{N}) , (List.\operatorname{ofFn} fun (i : Fin m) \mapsto u \operatorname{val}\left(i\right)) . length = m$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.pre_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite prefix made with List.ofFn has its specified length.

**Theorem 1.18 (pre_get).**

$$\forall (alpha : Type) (u : \mathbb{N} \to alpha) (m j : \mathbb{N}) , j < (List.\operatorname{ofFn} fun (i : Fin m) \mapsto u \operatorname{val}\left(i\right)) . length \to (List.\operatorname{ofFn} fun (i : Fin m) \mapsto u \operatorname{val}\left(i\right)) [j] = u j$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.pre_get` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Indexing the finite prefix reads the same position of the infinite word.

**Theorem 1.19 (pre_prefix).**

$$\forall (alpha : Type) (u : \mathbb{N} \to alpha) (m n : \mathbb{N}) ,m \leq n \to (List.\operatorname{ofFn} fun (i : Fin m) \mapsto u \operatorname{val}\left(i\right)) <+: (List.\operatorname{ofFn} fun (i : Fin n) \mapsto u \operatorname{val}\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.pre_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite prefix of the sequence is a prefix of every longer finite prefix.

**Theorem 1.20 (Generates.step).**

$$\forall (alpha : Type) (delta : \mathbb{N} \to alpha) (Theta : \mathbb{N} \to InvAntimorphism alpha) (u : \mathbb{N} \to alpha) (W : \mathbb{N} \to List alpha) , Generates delta Theta u W \to \forall (n : \mathbb{N}) , IsClosure (Theta (n + 1)) (W n ++ [delta (n + 1)]) (W (n + 1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each next stage closes the previous stage with the next directive letter appended.

**Theorem 1.21 (Generates.strict_growth).**

$$\forall (alpha : Type) (delta : \mathbb{N} \to alpha) (Theta : \mathbb{N} \to InvAntimorphism alpha) (u : \mathbb{N} \to alpha) (W : \mathbb{N} \to List alpha) , Generates delta Theta u W \to \forall (n : \mathbb{N}) , (W n) . length < (W (n + 1)) . length$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.strict_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Appending a letter before closure makes every stage strictly longer.

**Theorem 1.22 (Generates.length_ge).**

$$\forall (alpha : Type) (delta : \mathbb{N} \to alpha) (Theta : \mathbb{N} \to InvAntimorphism alpha) (u : \mathbb{N} \to alpha) (W : \mathbb{N} \to List alpha) , Generates delta Theta u W \to \forall (n : \mathbb{N}) , n \leq (W n) . length$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.length_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stage n has length at least n.

**Theorem 1.23 (Generates.nested_le).**

$$\forall (alpha : Type) (delta : \mathbb{N} \to alpha) (Theta : \mathbb{N} \to InvAntimorphism alpha) (u : \mathbb{N} \to alpha) (W : \mathbb{N} \to List alpha) , Generates delta Theta u W \to \forall (m n : \mathbb{N}) , m \leq n \to W m <+: W n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.nested_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stages are nested in the order of their indices.

**Theorem 1.24 (Generates.pal).**

$$\forall (alpha : Type) (delta : \mathbb{N} \to alpha) (Theta : \mathbb{N} \to InvAntimorphism alpha) (u : \mathbb{N} \to alpha) (W : \mathbb{N} \to List alpha) , Generates delta Theta u W \to \forall (n : \mathbb{N}) , 1 \leq n \to Function.\operatorname{IsFixedPt} (Theta n) . toFun (W n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.pal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each positive stage is fixed by its directive antimorphism.

**Theorem 1.25 (Generates.read).**

$$\forall (alpha : Type) (delta : \mathbb{N} \to alpha) (Theta : \mathbb{N} \to InvAntimorphism alpha) (u : \mathbb{N} \to alpha) (W : \mathbb{N} \to List alpha) , Generates delta Theta u W \to \forall (n j : \mathbb{N}) , j < (W n) . length \to (W n) [j] = u j$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A stage reads the infinite word at every index within its length.

**Definition 1.26 (IsNormalized).**

$$\forall (alpha : Type) (u : \mathbb{N} \to alpha) (W : \mathbb{N} \to List alpha) , IsNormalized u W \iff \forall (m : \mathbb{N}) , (\exists (theta : InvAntimorphism alpha) , theta.\operatorname{toFun} (List.\operatorname{ofFn} (fun (i : Fin (m)) \mapsto u \operatorname{val}\left(i\right))) = List.\operatorname{ofFn} (fun (i : Fin (m)) \mapsto u \operatorname{val}\left(i\right))) \to \exists (n : \mathbb{N}) , W n = List.\operatorname{ofFn} (fun (i : Fin (m)) \mapsto u \operatorname{val}\left(i\right))$$

*Formalization.* `D5/S1/Words/Palindromes/PseudopalindromicNormalization.IsNormalized` (`✓ std3`).

*Citation.* J. Florian, Ľ. Dvořáková (2016). *On periodicity of generalized pseudostandard words*. DOI: [10.37236/4771](https://doi.org/10.37236/4771). URL: <https://arxiv.org/abs/1508.02020>.

*Commentary.*

“A directive bi-sequence Λ=(Δ,Θ) of a binary generalized pseudostandard word 𝐮(Δ,Θ) is called normalized if the sequence of prefixes (wₙ)_n≥0 of 𝐮(Δ,Θ) contains all palindromic and E-palindromic prefixes of 𝐮(Δ,Θ).” Page 5, Section 3.3: “A normalized directive bi-sequence can be defined similarly as in Definition 2 over multiliteral alphabet.” Every prefix fixed by any involutory antimorphism occurs among the stages.

**Theorem 1.27 (Generates.lengths_strictMono).**

$$\forall (alpha : Type) (delta : \mathbb{N} \to alpha) (Theta : \mathbb{N} \to InvAntimorphism alpha) (u : \mathbb{N} \to alpha) (W : \mathbb{N} \to List alpha) , Generates delta Theta u W \to StrictMono fun (n : \mathbb{N}) \mapsto (W n) . length$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.lengths_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stage lengths form a strictly increasing sequence.

**Theorem 1.28 (Generates.normalization_exists).**

$$\forall (alpha : Type) (delta : \mathbb{N} \to alpha) (Theta : \mathbb{N} \to InvAntimorphism alpha) (u : \mathbb{N} \to alpha) (W : \mathbb{N} \to List alpha) , Generates delta Theta u W \to \exists (deltap : \mathbb{N} \to alpha) (Thetap : \mathbb{N} \to InvAntimorphism alpha) (Wp : \mathbb{N} \to List alpha) , Generates deltap Thetap u Wp \land IsNormalized u Wp$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PseudopalindromicNormalization.normalization_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Enumerate all lengths of fixed prefixes in increasing order. Earliest insertion supplies consecutive closure steps and gives a normalized directive generating the same word.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.Generates`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.InvAntimorphism`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.IsClosure`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.IsNormalized`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.closure_suffix_bound`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.finite_border_period`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.length_ge`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.lengths_strictMono`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.letter`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.letterInvolutive`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.map_singleton`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.map_word`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.nested_le`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.normalization_exists`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.pal`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.pal_wrap`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.palindrome_transport_iff`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.perm`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.perm_apply`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.perm_unique`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.pre_get`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.pre_length`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.pre_prefix`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.prefix_to_suffix`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.read`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.singletonExists`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.step`
- Truth anchor: `D5/S1/Words/Palindromes/PseudopalindromicNormalization.strict_growth`
