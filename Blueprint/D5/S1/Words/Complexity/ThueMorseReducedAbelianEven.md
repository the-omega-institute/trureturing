# Even Reduced Abelian Complexity

## Abstract

Two Thue-Morse letters decide the even-length gap in reduced abelian complexity.

Reduced abelian complexity counts the classes of factors of a given length, where collapsing each maximal constant run to one letter leaves words of equal length that rearrange into one another. For the Thue-Morse word the odd lengths already reduce to shorter ones. Campbell, Currie and Rampersad displayed a rule for the gap between lengths 4n and 4n+2 and left it unproved. That rule is proved here.

Indices and counts are natural numbers; the gap is taken in the integers and then read by absolute value. The letter t denotes the Thue-Morse word indexed from zero, so the two letters compared are at n and at 3n. R is the class count carried by the companion module, unchanged here. A factor with n edges spans n+1 positions, and its alternation count is the number of positions where the letter changes.

**Definition 1.1 (Fewest alternations at a length).**

$$\forall n \in \mathbb{N}, \operatorname{minAlt}\left(n\right) = \min_{{s \in \mathbb{N}}} \operatorname{alt}\left(n, s\right)$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorseReducedAbelianEven.minAlternations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Over all starting positions, the alternation count attains a least value. The Thue-Morse word takes only finitely many run patterns at each length, so the range is a bounded set of natural numbers and the infimum is attained.

**Definition 1.2 (Most alternations at a length).**

$$\forall n \in \mathbb{N}, \operatorname{maxAlt}\left(n\right) = \max_{{s \in \mathbb{N}}} \operatorname{alt}\left(n, s\right)$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorseReducedAbelianEven.maxAlternations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same range has a greatest element, attained at some start. The two extremes bracket every alternation count occurring at that length.

**Lemma 1.3 (Parity of the two extremes).**

$$\forall n \in \mathbb{N}, (\left(\operatorname{minAlt}\left(n\right) + \operatorname{maxAlt}\left(n\right)\right) \bmod 2 = 0) \iff \operatorname{t}\left(n\right) = \operatorname{t}\left(3 \cdot n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorseReducedAbelianEven.alternation_extrema_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induct strongly on n. Splitting n by parity relates the extremes at n to those at half of n, using how the alternation count behaves when one letter is appended. The odd branch closes with a fact about three consecutive Thue-Morse letters. The statement is the step that carries the arithmetic of the word into the counting argument.

**Theorem 1.4 (The even-length gap).**

$$\forall n \in \mathbb{N}, 0 < n \implies (\operatorname{t}\left(n\right) = \operatorname{t}\left(3 \cdot n\right) \implies \left|\operatorname{R}\left(4 \cdot n + 2\right) - \operatorname{R}\left(4 \cdot n\right)\right| = 0) \land (\operatorname{t}\left(n\right) \neq \operatorname{t}\left(3 \cdot n\right) \implies \left|\operatorname{R}\left(4 \cdot n + 2\right) - \operatorname{R}\left(4 \cdot n\right)\right| = 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorseReducedAbelianEven.reducedAbelianComplexity_even_difference` (`✓ std3`). ∎

*Resolves.* `Problems/campbell-currie-rampersad-eq-11` (proved) by `D5/S1/Words/Complexity/ThueMorseReducedAbelianEven.reducedAbelianComplexity_even_difference`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"campbell-currie-rampersad-eq-11","declaration_gid":"D5/S1/Words/Complexity/ThueMorseReducedAbelianEven.reducedAbelianComplexity_even_difference","resolution_kind":"proved"} -->

*Citation.* John M. Campbell, James Currie, Narad Rampersad (2025). *Reduced complexities for sequences over finite alphabets*. DOI: [10.48550/arXiv.2509.16034](https://doi.org/10.48550/arXiv.2509.16034).

*Commentary.*

The alternation counts realised at a fixed length fill an interval, so the class count is the size of a weighted interval fixed by the two extremes. Moving the length from 4n to 4n+2 shifts that interval by a controlled amount, and the gap between the two counts collapses to the difference of the extremes taken modulo two. The previous parity statement then decides it. The hypothesis on n is needed: at n equal to zero the gap is two.

## References

- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianEven.alternation_extrema_parity`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianEven.maxAlternations`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianEven.minAlternations`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianEven.reducedAbelianComplexity_even_difference`
- Dependency: [D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd](ThueMorseReducedAbelianOdd.md)
