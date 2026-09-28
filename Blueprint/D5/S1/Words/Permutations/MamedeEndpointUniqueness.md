# Extremal Endpoint Structure

## Abstract

Oscillation and attained extremal endpoints coincide for reduced consecutive words; opposite extremal maps force oscillation and common extremal endpoints determine words.

**Theorem 1.1 (Word reversal and inverse permutations).**

$${\operatorname {SingletonWord}\left(n, \operatorname {Inverse}\left(sigma\right), \operatorname {Reverse}\left(w\right)\right) \iff \operatorname {SingletonWord}\left(n, sigma, w\right)} \land {\operatorname {Oscillation}\left(\operatorname {Reverse}\left(w\right)\right) \iff \operatorname {Oscillation}\left(w\right)}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeEndpointUniqueness.word_reversal_invariants` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n, permutation sigma, and list w of natural generator indices, singletonWord(n,inverse(sigma),reverse(w)) is equivalent to singletonWord(n,sigma,w), and oscillation(reverse(w)) is equivalent to oscillation(w). No validity, reducedness, consecutiveness, or nonempty-word premise is needed for the equivalences. The proof reuses the adjacent-swap inverse product and reduced-word reversal. Strict internal peaks and valleys reverse in order, as do the full spike list and its absolute-difference segment lengths. Reversal exchanges the two weak-increasing alternatives of the unchanged oscillation definition. Empty and singleton lists are included. The spike-reversal argument is extracted from the existing endpoint-oscillation proof and is now reused by that proof and the reflected source theorem. This is a symbolic invariance result, not a finite test or a singleton-class count.

**Theorem 1.2 (Forced descent from a maximal first letter).**

$$\operatorname {ReducedConsecutive}\left(n, \operatorname {Cons}\left(M, a\right)\right) \land \operatorname {AllLettersAtMost}\left(M, \operatorname {Cons}\left(M, a\right)\right) \implies \exists i , \exists q , \operatorname {InitialDescendingRun}\left(M, i, a, q\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeEndpointUniqueness.maximum_peel` (`✓ std3`). ∎

*Citation.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

For a reduced consecutive word M::a with every generator at most M, there are i and q with 1<=i<=M, M::a=descending(M,i)++q, and every letter of q strictly above i. Its product sends position i to position M+1. The descent is an initial run, with no assumed oscillation. The theorem is the existing forced-run proof exposed for reuse by the endpoint-uniqueness proof; it does not constrain all later spike lengths or establish Lemma 3.2's oscillation direction.

**Theorem 1.3 (Oscillation from an extremal endpoint).**

$$\operatorname {ReducedConsecutive}\left(n, w\right) \land \operatorname {Endpoint}\left(k, w\right) \land \operatorname {GeneratorExtremum}\left(k, w\right) \implies \operatorname {Oscillation}\left(w\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeEndpointUniqueness.extremal_endpoint_oscillation` (`✓ std3`). ∎

*Citation.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

Let w be a reduced consecutive adjacent-swap word on n+1 positions. Suppose its first or last letter is k, and all its letters are at most k or all are at least k. Then oscillation(w) holds: the absolute differences between its first letter, strict internal peaks and valleys, and last letter form a weakly increasing or weakly decreasing list. The endpoint condition excludes the empty word and makes k an attained extremum. A maximal first letter forces a descending run; its final letter starts a shorter suffix at its minimum. Reflection and induction give weakly decreasing lengths, and reversal supplies the last-letter cases. This proves the endpoint-to-oscillation direction of Lemma 3.2 in the repository's exact model. The paper invokes its Theorem 2.2, but this proof uses the existing reduced-word crossing results. It is paired with the reverse endpoint characterization below. The separate opposite-map theorem below derives the required extremal endpoint.

**Theorem 1.4 (An oscillating word has an extremal endpoint).**

$$\operatorname {Consecutive}\left(a\right) \land \operatorname {Member}\left(m, a\right) \land \operatorname {Member}\left(M, a\right) \land \operatorname {AllLettersBetween}\left(m, M, a\right) \land \operatorname {Oscillation}\left(a\right) \implies \operatorname {HeadEquals}\left(a, m\right) \lor \operatorname {HeadEquals}\left(a, M\right) \lor \operatorname {LastEquals}\left(a, m\right) \lor \operatorname {LastEquals}\left(a, M\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeEndpointUniqueness.oscillation_extremal_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural numbers m and M and a list a of natural generator indices, suppose a is consecutive, both m and M occur in a, every letter k satisfies m<=k<=M, and oscillation(a) holds. Then the first or last letter is m or M. The theorem needs no reducedness or permutation premise. It erases straight-run interior letters while preserving spikes, then uses monotone spike lengths to make the last letter an attained support extremum; reversal handles the opposite direction. This closes the reverse endpoint direction of Lemma 3.2 in the repository's word predicate under the stated attained-extrema and support hypotheses. The paper's commutation-class interpretation, global Conjecture 5.1 count, and the model translation are not proved.

**Theorem 1.5 (No two exterior factors around a symmetric excursion).**

$$\operatorname {ReducedConsecutiveSymmetricExcursion}\left(n, m, M, p, q\right) \land \operatorname {InteriorSupport}\left(m, M, p, q\right) \implies p = \operatorname {EmptyWord}\left(\right) \lor q = \operatorname {EmptyWord}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeOppositeExtremalMaps.symmetric_excursion_outer_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let 1<=m<M<=n and let the middle word descend from M to m, then ascend from m+1 to M. If p and q contain only generators strictly between m and M, and the combined word is reduced and consecutive, then p or q is empty. The middle product swaps positions m and M+1 and fixes the interior. When both factors are nonempty, consecutiveness forces generator M-1 at both boundaries; the two copies commute through the middle product and cancel, contradicting reducedness. This is an unbounded source theorem. It does not derive the displayed factorization from opposite endpoint maps or prove their oscillation consequence.

**Theorem 1.6 (Oscillation from both extremal position maps).**

$$\operatorname {SingletonWord}\left(n, sigma, a\right) \land \operatorname {AttainedGeneratorExtrema}\left(m, M, a\right) \land \operatorname {GeneratorInterval}\left(n, m, M, a\right) \land \operatorname {OppositeExtremalMaps}\left(n, m, M, sigma\right) \implies \operatorname {Oscillation}\left(a\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeOppositeExtremalMaps.opposite_extremal_maps_oscillation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a be a singletonWord for sigma, so a is reduced and consecutive and its product is sigma. Suppose m and M both occur in a, 1<=m<=M<=n, and every letter k satisfies m<=k<=M. If sigma sends position M+1 to m and position m to M+1 simultaneously, then oscillation(a). For m=M the word begins at its attained minimum. For m<M, exterior fixedness and the guarded strand walk force a full descent in a and another full descent in its reverse, hence a full ascent in a. Comparing the run prefixes aligns them at m or M; the two occurrences of m are not assumed equal. The resulting descent-then-ascent or ascent-then-descent excursion has strictly interior outer factors. The symmetric-excursion obstruction, with generator reflection for the second orientation, makes one factor empty. An actual extremal first or last letter then supplies the endpoint-oscillation theorem. No oscillation, source shape, exterior fixedness, or word endpoint is an input. This is the implication for the explicit attained-generator interval, not a global fiber count.

**Theorem 1.7 (Uniqueness at either end).**

$$\operatorname {ReducedConsecutive}\left(n, a\right) \land \operatorname {ReducedConsecutive}\left(n, b\right) \land \operatorname {WordProduct}\left(n, a\right) = \operatorname {WordProduct}\left(n, b\right) \land \operatorname {CommonEndpoint}\left(k, a, b\right) \land \operatorname {CommonExtremum}\left(k, a, b\right) \implies a = b$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeEndpointUniqueness.extremal_endpoint_unique` (`✓ std3`). ∎

*Citation.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

Let a and b be reduced consecutive adjacent-swap words on n+1 positions with the same permutation product. Suppose both first letters are k, or both last letters are k. Suppose also that every letter of both words is at most k, or every letter of both words is at least k. Then a=b. The endpoint condition excludes empty words. The minimum and maximum alternatives apply separately, and the compared endpoints are on the same side. No oscillation assumption is needed: this is the endpoint-extremum form of Mamede, Santos and Soares, Lemmas 3.2 and 3.4. For a maximal first letter, the largest strand forces a common initial descent. Removing it leaves shorter words starting at their minimum, so induction determines the tails. Reflection gives the minimal-first case; reversal gives the last-letter cases. The result compares words at an extremal endpoint. It does not assert uniqueness for arbitrary endpoints or for an entire singleton-word fiber.

## References

- Truth anchor: `D5/S1/Words/Permutations/MamedeEndpointUniqueness.extremal_endpoint_oscillation`
- Truth anchor: `D5/S1/Words/Permutations/MamedeEndpointUniqueness.extremal_endpoint_unique`
- Truth anchor: `D5/S1/Words/Permutations/MamedeEndpointUniqueness.maximum_peel`
- Truth anchor: `D5/S1/Words/Permutations/MamedeEndpointUniqueness.oscillation_extremal_endpoint`
- Truth anchor: `D5/S1/Words/Permutations/MamedeEndpointUniqueness.word_reversal_invariants`
- Truth anchor: `D5/S1/Words/Permutations/MamedeOppositeExtremalMaps.opposite_extremal_maps_oscillation`
- Truth anchor: `D5/S1/Words/Permutations/MamedeOppositeExtremalMaps.symmetric_excursion_outer_empty`
- Dependency: [D5/S1/Words/Permutations/MamedeCrossing](MamedeCrossing.md)
- Dependency: [D5/S1/Words/Permutations/MamedeExtremalOrientation](MamedeExtremalOrientation.md)
