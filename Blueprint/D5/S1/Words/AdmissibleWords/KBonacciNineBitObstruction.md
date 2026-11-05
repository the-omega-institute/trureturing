# A simultaneous obstruction through nine bits

## Abstract

The two raw remainders of 1 + X cannot be acquired by one order-two legal Boolean word using at most nine actual positions.

Work over ZMod 2. A word w of length n is a function from Fin n to Bool, read with position zero first, and P(w) is its original word polynomial: the coefficient of X^j is one exactly when w(j) is true. The predicate A(n,w) is DBonacciAdmissible 2 n w, the original scanner excluding two consecutive true bits. Every false bit counts toward n, and n may be zero.

Let r_a(P) be the raw monic remainder P modulo Phi_a, where Phi_a is X^a minus the sum of X^j for zero <= j < a. Both observations below read the same word. No tail or phase condition is imposed.

**Definition 1.1 (The proposed common short realization).**

$$claim \Leftrightarrow \left(\exists n \in \mathbb{N},\; n \le 9 \land \left(\exists w \in \operatorname{Fin}\left(n\right) \to \operatorname{Bool},\; \operatorname{A}\left(n, w\right) \land \left(\operatorname{r}\left(2, \operatorname{P}\left(w\right)\right) = \operatorname{r}\left(2, 1 + X\right) \land \operatorname{r}\left(3, \operatorname{P}\left(w\right)\right) = \operatorname{r}\left(3, 1 + X\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/AdmissibleWords/KBonacciNineBitObstruction.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The claim asks for one length at most nine and one accepted word whose two raw remainders equal the corresponding remainders of 1 + X. Separate words for the two coordinates do not satisfy this claim.

**Theorem 1.2 (There is no common short realization).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciNineBitObstruction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nine-position word, write b_j for its bit as an element of ZMod 2. Monic division yields the two coefficient rows b_0+b_2+b_3+b_5+b_6+b_8 and b_1+b_2+b_4+b_5+b_7+b_8 for Phi_2. The three rows for Phi_3 are b_0+b_3+b_4+b_7+b_8, b_1+b_3+b_5+b_7, and b_2+b_3+b_6+b_7. The target requires these five values to be 1, 1, 1, 1, and 0, respectively.

Explicit quotient identities establish these remainder formulas for every nine-position word. A finite decision over all functions from Fin 9 to Bool then excludes the five equations together with acceptance by the original scanner. Appending a false bit preserves both the word polynomial and scanner acceptance, so any shorter realization would give an excluded nine-position realization.

This exclusion gives the lower bound for the specified target. It does not assert attainment at ten, identify the whole common image, or establish an exact saturation threshold.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciNineBitObstruction.claim`
- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciNineBitObstruction.result`
- Dependency: [D5/S1/Words/AdmissibleWords/KBonacciActualSaturation](KBonacciActualSaturation.md)
