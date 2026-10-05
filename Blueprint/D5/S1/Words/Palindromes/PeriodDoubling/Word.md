# The Period-Doubling Word

## Abstract

The literal substitution fixed word agrees with positive-position valuation parity.

**Definition 1.1 (The source substitution).**

$$\forall b \in \operatorname{Bool},\; \operatorname{pdMorphism}\left(b\right) = [\operatorname{false},\operatorname{not}\left(b\right)]$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/Word.pdMorphism` (`✓ std3`).

*Citation.* Anna E. Frid, Enzo Laborde, and Jarkko Peltomäki (2021). *On prefix palindromic length of automatic words*. DOI: [10.1016/j.tcs.2021.08.016](https://doi.org/10.1016/j.tcs.2021.08.016). URL: <https://arxiv.org/abs/2009.02934v2>.

*Commentary.*

Section 5.1, printed page 12: “The period-doubling word u_pd is the 2-automatic word” u_pd = φ_pd^ω(a) = abaaabababaaabaa…, with φ_pd(a) = ab and φ_pd(b) = aa. Here a is false and b is true; the displayed list is that substitution literally.

**Definition 1.2 (Literal substitution approximants).**

$$\forall e \in \mathbb{N},\; \operatorname{pdBlock}\left(e\right) = \operatorname{morphismPower}\left(\operatorname{pdMorphism}, e, [\operatorname{false}]\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/Word.pdBlock` (`✓ std3`).

*Citation.* Anna E. Frid, Enzo Laborde, and Jarkko Peltomäki (2021). *On prefix palindromic length of automatic words*. DOI: [10.1016/j.tcs.2021.08.016](https://doi.org/10.1016/j.tcs.2021.08.016). URL: <https://arxiv.org/abs/2009.02934v2>.

*Commentary.*

The e-th approximant is the e-th morphism iterate of the one-letter word a. Iteration is the existing morphismPower operation.

**Definition 1.3 (The infinite fixed word).**

$$\forall n \in \mathbb{N},\; \left(u_{\mathrm{pd}}\right)\left(n\right) = \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{pdBlock}\left(n + 1\right), n\right), \operatorname{false}\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/Word.u_pd` (`✓ std3`).

*Citation.* Anna E. Frid, Enzo Laborde, and Jarkko Peltomäki (2021). *On prefix palindromic length of automatic words*. DOI: [10.1016/j.tcs.2021.08.016](https://doi.org/10.1016/j.tcs.2021.08.016). URL: <https://arxiv.org/abs/2009.02934v2>.

*Commentary.*

Section 5.1, printed page 12: “The period-doubling word u_pd is the 2-automatic word” u_pd = φ_pd^ω(a) = abaaabababaaabaa…, with φ_pd(a) = ab and φ_pd(b) = aa. The zero-based n-th symbol is read from phi_pd^(n+1)(a); the block theorem proves that this position is covered and agrees with every longer approximant. getElemOption is optional list indexing and getD supplies its stated default.

**Theorem 1.4 (Every approximant has the valuation letters).**

$$\forall e \in \mathbb{N},\; \operatorname{length}\left(\operatorname{pdBlock}\left(e\right)\right) = 2^{e} \land \left(\forall i \in \mathbb{N},\; i < 2^{e} \Rightarrow \operatorname{getElemOption}\left(\operatorname{pdBlock}\left(e\right), i\right) = \operatorname{some}\left(\operatorname{decide}\left(\operatorname{mod}\left(\operatorname{padicValNat}\left(2, i + 1\right), 2\right) = 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/Word.block_valuation` (`✓ std3`). ∎

*Citation.* Shuo Li (2020). *Palindromic length sequence of the ruler sequence and of the period-doubling sequence*. URL: <https://arxiv.org/abs/2007.08317v1>.

*Commentary.*

Li, printed page 2: “The other one is the period-doubling sequence (A096268 in OEIS), which can be defined as the fixed point of the two substitution 0 → 01, 1 → 00 with initial word 0.” “We know that this sequence can also be defined as the sequence (a[n])ₙ∈ℕ⁺ modulo 2.” Positive position i+1 has symbol determined by v_2(i+1) modulo two. The theorem also proves the exact iterate length. mod is the natural-number remainder; decide converts a proposition to a Boolean.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/Word.block_valuation`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/Word.pdBlock`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/Word.pdMorphism`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/Word.u_pd`
- Dependency: [D5/S1/Recurrence/Raney/MaximalBlockEvolution](../../../Recurrence/Raney/MaximalBlockEvolution.md)
