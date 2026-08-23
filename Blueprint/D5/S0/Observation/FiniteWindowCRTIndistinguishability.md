# Finite-Window CRT Indistinguishability

## Abstract

Every finite coprime residue window is realized by a natural-number shift, with an explicit three-modulus certificate.

**Theorem 1.1 (A finite coprime window cannot separate a shift).**

$$\forall W: \operatorname{Finset}\left(\mathbb{N}\right), (\forall m, m \in W \Rightarrow 0 < m \land \forall m, n, (m \in W \land n \in W \land m \neq n) \Rightarrow \operatorname{Coprime}\left(m, n\right)) \Rightarrow \operatorname{Surjective}\left(\operatorname{windowReading}\left(W\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Observation/FiniteWindowCRTIndistinguishability.finite_window_cannot_separate_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite collection of positive pairwise-coprime natural moduli, the window-reading map is onto the dependent product of the corresponding residue rings. Thus one natural number realizes every prescribed residue in the window simultaneously.

The construction chooses natural representatives for the target residues, applies the finite Chinese remainder theorem, and then identifies the resulting congruences with equality in each ZMod component. The witness depends on both the finite window and the target; no single shift is asserted to realize all windows at once.

**Lemma 1.2 (The four-nine-twenty-five window has an explicit certificate).**

$$\operatorname{card}\left(\operatorname{ZMod}\left(4\right) \times \operatorname{ZMod}\left(9\right) \times \operatorname{ZMod}\left(25\right)\right) = 900 \land 511 \equiv 3 (\operatorname{mod} 4) \land 511 \equiv 7 (\operatorname{mod} 9) \land 511 \equiv 11 (\operatorname{mod} 25).$$

*Proof.* Machine-checked in Lean as `D5/S0/Observation/FiniteWindowCRTIndistinguishability.window_4_9_25_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product of the residue rings modulo four, nine, and twenty-five has exactly nine hundred elements. The natural number 511 reads as 3 modulo 4, 7 modulo 9, and 11 modulo 25.

This supplies one concrete realization in a pairwise-coprime observation window. It is an existence certificate, not a uniqueness claim and not a replacement for the general surjectivity theorem.

## References

- Truth anchor: `D5/S0/Observation/FiniteWindowCRTIndistinguishability.finite_window_cannot_separate_shift`
- Truth anchor: `D5/S0/Observation/FiniteWindowCRTIndistinguishability.window_4_9_25_certificate`
