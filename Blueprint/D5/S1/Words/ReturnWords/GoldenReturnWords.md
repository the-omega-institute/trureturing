# Return Words of the Golden Word: the Length-One Case

## Abstract

Define golden return words, prove existence for every occurring factor, and classify the two return words of each length-one factor.

**Definition 1.1 (Adjacent occurrences have no intervening start).**

Lean statement: `D5/S1/Words/ReturnWords/GoldenReturnWords.AdjacentGoldenOccurrences`

*Formalization.* `D5/S1/Words/ReturnWords/GoldenReturnWords.AdjacentGoldenOccurrences` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

AdjacentGoldenOccurrences n w i j means that i is strictly before j, the length-n golden factors at both starts equal w, and no start strictly between i and j carries the same factor.

**Definition 1.2 (A return word is the block between adjacent starts).**

Lean statement: `D5/S1/Words/ReturnWords/GoldenReturnWords.IsGoldenReturnWord`

*Formalization.* `D5/S1/Words/ReturnWords/GoldenReturnWords.IsGoldenReturnWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A list r is a return word to w when adjacent occurrences of w start at i and j and r is the golden factor of length j-i beginning at i.

**Definition 1.3 (Return words are collected as a set).**

Lean statement: `D5/S1/Words/ReturnWords/GoldenReturnWords.goldenReturnWords`

*Formalization.* `D5/S1/Words/ReturnWords/GoldenReturnWords.goldenReturnWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

goldenReturnWords n w is the set of all lists satisfying the return-word predicate. Finiteness is proved here only for length one.

**Theorem 1.4 (Every occurring golden factor has a return word).**

$$w\in\operatorname{goldenFactorSet}(n) \Rightarrow \operatorname{goldenReturnWords}(n,w)\neq\emptyset$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenReturnWords.golden_return_words_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Recurrence supplies an occurrence later than a chosen start. Nat.find selects the least such later start; its minimality excludes every intermediate occurrence and therefore supplies an adjacent pair.

**Theorem 1.5 (The true factor has return words T and TF).**

$$\operatorname{goldenReturnWords}(1,T)=\{T,TF\}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenReturnWords.golden_return_words_true` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Balance rules out two consecutive false letters by comparison with the known TT window. Hence adjacent true starts differ by one or two, giving T and TF. Starts (2,3) and (0,2) realize both cases.

**Theorem 1.6 (The false factor has return words FT and FTT).**

$$\operatorname{goldenReturnWords}(1,F)=\{FT,FTT\}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenReturnWords.golden_return_words_false` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absence of FF forces a true letter between false starts. Balance also rules out TTT by comparison with the known FTF window, so the gap is two or three. Starts (4,6) and (1,4) realize both values.

**Theorem 1.7 (Every length-one factor has exactly two return words).**

$$w\in\operatorname{goldenFactorSet}(1) \Rightarrow \operatorname{encard}(\operatorname{goldenReturnWords}(1,w))=2$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenReturnWords.golden_return_words_encard_eq_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every member of goldenFactorSet 1 has length one, hence is T or F. The two explicit set equalities give extended cardinality two.

The length-two occurrence-gap spectra are global: TF and FT have {2,3}, while TT has {3,5}; each therefore has encard two. This does not claim the all-n theorem. That theorem remains deferred until admissible_rotation_gap_first_returns_two is proved without new axioms.

**Theorem 1.8 (Seed substitution preserves return membership at synchronized markers).**

$$r\in R_1(b) \Rightarrow \operatorname{subst}(r)\in R_2(\operatorname{marker}(b))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenReturnWords.seed_return_word_subst_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For b=true the synchronized image marker is TF; for b=false it is TT. The marker is essential: the naive claim using subst(F)=T is false because subst(FT)=TTF is not a return word to T.

## References

- Truth anchor: `D5/S1/Words/ReturnWords/GoldenReturnWords.AdjacentGoldenOccurrences`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenReturnWords.IsGoldenReturnWord`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenReturnWords.goldenReturnWords`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenReturnWords.golden_return_words_encard_eq_two`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenReturnWords.golden_return_words_false`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenReturnWords.golden_return_words_nonempty`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenReturnWords.golden_return_words_true`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenReturnWords.seed_return_word_subst_mem`
- Dependency: [D5/S1/Words/GoldenSubstFixed](../GoldenSubstFixed.md)
- Dependency: [D5/S1/Words/GoldenUniformRecurrence](../GoldenUniformRecurrence.md)
