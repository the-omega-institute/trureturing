# A parity obstruction for universal-input morphisms

## Abstract

A finite morphism of a word containing every finite source word cannot have positive constant even additive complexity.

Sahasrabudhe's question concerns concatenating all finite words and then applying a finite morphism. Here the source alphabet is any finite nonempty type, every finite source list occurs contiguously, and the output consists of integer letters. Empty images are allowed; the cumulative boundaries must be unbounded. The conclusion concerns this construction and does not exclude other words of constant even additive complexity.

**Definition 1.1 (Every finite source word occurs).**

$$\forall \alpha: \operatorname{Type}, \forall w: \mathbb{N} \to \alpha, \operatorname{UniversalInput}\left(w\right) = (\forall u: \operatorname{List}\left(\alpha\right), \exists i: \mathbb{N}, \operatorname{List.ofFn}\left(\operatorname{wordFactor}\left(w, \operatorname{List.length}\left(u\right), i\right)\right) = u)$$

*Formalization.* `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.UniversalInput` (`✓ std3`).

*Citation.* Julian Sahasrabudhe (2015). *Sturmian Words and Constant Additive Complexity*. DOI: [10.5281/zenodo.10456215](https://doi.org/10.5281/zenodo.10456215). URL: <https://math.colgate.edu/~integers/p30/p30.pdf>.

*Commentary.*

Section 5, printed p. 7: “Indeed, enumerate all words of finite length on the alphabet {0, . . . , n}, and form an infinite word w by concatenating all of the finite words in the order specified by the enumeration.” The predicate retains the resulting occurrence property: each finite list appears at a natural starting position. List.ofFn converts the length-indexed wordFactor to a list. Indices start at zero, including the empty list.

**Definition 1.2 (The infinite concatenated output).**

$$\forall \alpha: \operatorname{Type}, \forall w: \mathbb{N} \to \alpha, \forall \phi: \alpha \to \operatorname{List}\left(\mathbb{Z}\right), \forall y: \mathbb{N} \to \mathbb{Z}, \operatorname{IsMorphicImage}\left(w, \phi, y\right) = (\exists b: \mathbb{N} \to \mathbb{N}, (b\left(0\right) = 0) \land ((\operatorname{Monotone}\left(b\right)) \land ((\forall i: \mathbb{N}, b\left(i + 1\right) = b\left(i\right) + \operatorname{List.length}\left(\phi\left(w\left(i\right)\right)\right)) \land ((\forall N: \mathbb{N}, \exists i: \mathbb{N}, N < b\left(i\right)) \land (\forall i: \mathbb{N}, \forall j: \mathbb{N}, \forall h: j < \operatorname{List.length}\left(\phi\left(w\left(i\right)\right)\right), y\left(b\left(i\right) + j\right) = \operatorname{List.get}\left(\phi\left(w\left(i\right)\right), \langle j, h\rangle\right))))))$$

*Formalization.* `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.IsMorphicImage` (`✓ std3`).

*Citation.* Julian Sahasrabudhe (2015). *Sturmian Words and Constant Additive Complexity*. DOI: [10.5281/zenodo.10456215](https://doi.org/10.5281/zenodo.10456215). URL: <https://math.colgate.edu/~integers/p30/p30.pdf>.

*Commentary.*

Section 5, printed p. 7: “Then apply the morphism defined by” precedes the images 0 ↦ (0)(2n), 1 ↦ (1)(2n − 1), …, n ↦ (n)(n). For an arbitrary map from source letters to finite integer lists, b records the cumulative lengths, begins at zero, is monotone and unbounded, and each output segment agrees with the corresponding codeword. A zero-length image contributes no letters.

**Definition 1.3 (Sum of a contiguous factor).**

$$\forall y: \mathbb{N} \to \mathbb{Z}, \forall n: \mathbb{N}, \forall i: \mathbb{N}, \operatorname{factorSum}\left(y, n, i\right) = \sum_{j: \operatorname{Fin}\left(n\right)} y\left(i + \operatorname{val}\left(j\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.factorSum` (`✓ std3`).

*Citation.* Julian Sahasrabudhe (2015). *Sturmian Words and Constant Additive Complexity*. DOI: [10.5281/zenodo.10456215](https://doi.org/10.5281/zenodo.10456215). URL: <https://math.colgate.edu/~integers/p30/p30.pdf>.

*Commentary.*

Section 2, printed p. 1: “A block b of a word w is a sequence of consecutive elements of w, that is b = wₖ ··· wₖ′ for k ≤ k′.” “For a block b = wₖ ··· wₖ′ of w, we define Σb := ∑ᵢ₌ₖᵏ′ wᵢ.” The displayed sum uses j : Fin n and starts at i, so it contains exactly n terms. The value of j in the addition is its natural-number value.

**Definition 1.4 (All sums at a fixed length).**

$$\forall y: \mathbb{N} \to \mathbb{Z}, \forall n: \mathbb{N}, \operatorname{sumSet}\left(y, n\right) = \{z: \mathbb{Z} | \exists i: \mathbb{N}, \operatorname{factorSum}\left(y, n, i\right) = z\}$$

*Formalization.* `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.sumSet` (`✓ std3`).

*Citation.* Julian Sahasrabudhe (2015). *Sturmian Words and Constant Additive Complexity*. DOI: [10.5281/zenodo.10456215](https://doi.org/10.5281/zenodo.10456215). URL: <https://math.colgate.edu/~integers/p30/p30.pdf>.

*Commentary.*

Section 2, printed p. 2: “The additive complexity of an infinite word w over a finite set of integers is the function ρ⁺(w, n) that counts the number of distinct sums obtained by summing n consecutive symbols of w.” The set ranges over every natural starting position; equal sums are represented once.

**Definition 1.5 (Number of distinct sums).**

$$\forall y: \mathbb{N} \to \mathbb{Z}, \forall n: \mathbb{N}, \operatorname{additiveComplexity}\left(y, n\right) = \operatorname{Set.ncard}\left(\operatorname{sumSet}\left(y, n\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.additiveComplexity` (`✓ std3`).

*Citation.* Julian Sahasrabudhe (2015). *Sturmian Words and Constant Additive Complexity*. DOI: [10.5281/zenodo.10456215](https://doi.org/10.5281/zenodo.10456215). URL: <https://math.colgate.edu/~integers/p30/p30.pdf>.

*Commentary.*

Section 2, printed p. 2: “The additive complexity of an infinite word w over a finite set of integers is the function ρ⁺(w, n) that counts the number of distinct sums obtained by summing n consecutive symbols of w.” Set.ncard gives this cardinality for finite sets. Its value on an infinite set is zero; the contradictory positive constant assumption in the proof ensures finiteness whenever the parity argument uses it. Only positive lengths enter the conclusion.

**Definition 1.6 (The finite-morphism construction question).**

$$\operatorname{claim} = (\forall \alpha: \operatorname{Type}, [\operatorname{Fintype}\left(\alpha\right)] [\operatorname{Nonempty}\left(\alpha\right)], \forall w: \mathbb{N} \to \alpha, \forall \phi: \alpha \to \operatorname{List}\left(\mathbb{Z}\right), \forall y: \mathbb{N} \to \mathbb{Z}, (\operatorname{UniversalInput}\left(w\right)) \Rightarrow ((\operatorname{IsMorphicImage}\left(w, \phi, y\right)) \Rightarrow (\neg (\exists k: \mathbb{N}, (0 < k) \land (\forall n: \mathbb{N}, (0 < n) \Rightarrow (\operatorname{additiveComplexity}\left(y, n\right) = 2 \cdot k))))))$$

*Formalization.* `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.claim` (`✓ std3`).

*Citation.* Julian Sahasrabudhe (2015). *Sturmian Words and Constant Additive Complexity*. DOI: [10.5281/zenodo.10456215](https://doi.org/10.5281/zenodo.10456215). URL: <https://math.colgate.edu/~integers/p30/p30.pdf>.

*Commentary.*

Section 5, printed p. 7: “Can a construction of this form be generalized to give constructions of words with fixed even complexity?” The proposition answers the question negatively for every finite nonempty source alphabet and every universal source word. The map assigns a finite integer list to each letter. Its infinite output cannot have 2k distinct length-n sums for all positive n with k positive. Source indices are translated to zero-based natural indices, with no change in factor lengths or counts.

**Theorem 1.7 (Exact intervals between cumulative boundaries).**

$$\forall \alpha: \operatorname{Type}, \forall w: \mathbb{N} \to \alpha, \forall \phi: \alpha \to \operatorname{List}\left(\mathbb{Z}\right), \forall y: \mathbb{N} \to \mathbb{Z}, \forall b: \mathbb{N} \to \mathbb{N}, (\operatorname{Monotone}\left(b\right)) \Rightarrow ((\forall i: \mathbb{N}, b\left(i + 1\right) = b\left(i\right) + \operatorname{List.length}\left(\phi\left(w\left(i\right)\right)\right)) \Rightarrow ((\forall i: \mathbb{N}, \forall j: \mathbb{N}, (j < \operatorname{List.length}\left(\phi\left(w\left(i\right)\right)\right)) \Rightarrow (y\left(b\left(i\right) + j\right) = \operatorname{List.get}\left(\phi\left(w\left(i\right)\right), j\right))) \Rightarrow (\forall s: \mathbb{N}, \forall t: \mathbb{N}, \operatorname{List.ofFn}\left(\operatorname{wordFactor}\left(y, b\left(s + t\right) - b\left(s\right), b\left(s\right)\right)\right) = \operatorname{List.flatMap}\left(\phi, \operatorname{List.ofFn}\left(\operatorname{wordFactor}\left(w, t, s\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.morphic_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any source type, source stream, integer-valued finite codewords, integer output stream and monotone natural boundaries, the step law and every local codeword letter equation identify the entire interval from b(s) to b(s+t) with the flatMap of the actual length-t source factor. Neither a universal source nor unbounded boundaries is required for this finite interval identity. Zero-length codewords and t=0 remain in scope.

**Theorem 1.8 (No positive constant even complexity).**

$$\forall \alpha: \operatorname{Type}, [\operatorname{Fintype}\left(\alpha\right)] [\operatorname{Nonempty}\left(\alpha\right)], \forall w: \mathbb{N} \to \alpha, \forall \phi: \alpha \to \operatorname{List}\left(\mathbb{Z}\right), \forall y: \mathbb{N} \to \mathbb{Z}, (\operatorname{UniversalInput}\left(w\right)) \Rightarrow ((\operatorname{IsMorphicImage}\left(w, \phi, y\right)) \Rightarrow (\neg (\exists k: \mathbb{N}, (0 < k) \land (\forall n: \mathbb{N}, (0 < n) \Rightarrow (\operatorname{additiveComplexity}\left(y, n\right) = 2 \cdot k)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.result` (`✓ std3`). ∎

*Resolves.* `Problems/sahas2015` (proved) by `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sahas2015","declaration_gid":"D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Julian Sahasrabudhe (2015). *Sturmian Words and Constant Additive Complexity*. DOI: [10.5281/zenodo.10456215](https://doi.org/10.5281/zenodo.10456215). URL: <https://math.colgate.edu/~integers/p30/p30.pdf>.

*Commentary.*

If all positive-length sum counts had one positive constant value, equal-length complete images would have equal sums: otherwise powers of two such images give too many distinct sums at a common length. The semigroup generated by codeword lengths contains every sufficiently large multiple of their gcd. Choose such a length n large enough to bracket each length-n factor by codeword boundaries and pad the bracket to length 2n. A doubled source word supplies both the factor and its complement in a cyclic rotation of this complete image. The length-n sum set is therefore invariant under reflection about the sum of a complete image of length n. That central sum occurs, and the other sums pair off, giving an odd count and a contradiction. Unbounded boundaries handle empty codewords in the same argument.

## References

- Truth anchor: `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.IsMorphicImage`
- Truth anchor: `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.UniversalInput`
- Truth anchor: `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.additiveComplexity`
- Truth anchor: `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.claim`
- Truth anchor: `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.factorSum`
- Truth anchor: `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.morphic_block`
- Truth anchor: `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.result`
- Truth anchor: `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.sumSet`
- Dependency: [D5/S1/Words/Complexity/MorseHedlund](MorseHedlund.md)
