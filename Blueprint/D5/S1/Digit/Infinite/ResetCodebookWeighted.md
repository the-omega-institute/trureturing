# Reset codebook: Weighted

## Abstract

Reset codebooks, actual sources and weighted lower-memory graphs.

**Theorem 1.1 (codebook finite).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookWeighted.codebook_finite`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookWeighted.codebook_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (anchor : Bool) (K N : ℕ) (d : ℝ) : (D5.S1.Digit.Infinite.ResetCodebook.Statement.codebook anchor K N d).Finite

**Theorem 1.2 (letter length le weight).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookWeighted.letter_length_le_weight`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookWeighted.letter_length_le_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (w : List Bool) : w.length ≤ Statement.letterWeight w

**Theorem 1.3 (weightedReadout bounded).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookWeighted.weightedReadout_bounded`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookWeighted.weightedReadout_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (lang : Set (ℤ → Bool)) : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (weightedReadout lang)

**Theorem 1.4 (complete lower language count and rate).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookWeighted.complete_lower_language_count_and_rate`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookWeighted.complete_lower_language_count_and_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (anchor : Bool) (K M N n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hM : 1 ≤ M) (hreset : initial false anchor < Statement.B M) (hcut : h false*rho^n < chi^(K-1)*(Statement.B M-initial false anchor)*g^N) (hne : (Statement.codebook anchor K N d).Nonempty) : (∀ k, (Nat.card (WeakBook anchor K N d))^k ≤ Statement.factorCount (Statement.lowerLanguage K n d) (k*(N+20+6*M))) ∧ Real.log (Nat.card (WeakBook anchor K N d):ℝ)/Real.log 2/(N+20+6*M:ℝ) ≤ Statement.rate (Statement.lowerLanguage K n d)

## References

- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookWeighted.codebook_finite`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookWeighted.complete_lower_language_count_and_rate`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookWeighted.letter_length_le_weight`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookWeighted.weightedReadout_bounded`
- Dependency: [D5/S0/Computability/Coding/PrefixFreeCode](../../../S0/Computability/Coding/PrefixFreeCode.md)
- Dependency: [D5/S1/Digit/Infinite/ResetCodebookIndexed](ResetCodebookIndexed.md)
