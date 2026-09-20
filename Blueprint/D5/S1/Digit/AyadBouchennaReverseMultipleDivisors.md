# Divisors of All Reversed Multiples

## Abstract

Divisors of B squared minus one are exactly the positive divisors of all their reversed base-B multiples.

**Definition 1.1 (Reversal in a base).**

$$\forall B \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{reverseBase}\left(B, m\right) = \operatorname{ofDigits}\left(B, \operatorname{reverse}\left(\operatorname{digits}\left(B, m\right)\right)\right)$$

*Formalization.* `D5/S1/Digit/AyadBouchennaReverseMultipleDivisors.reverseBase` (`✓ std3`).

*Citation.* Mohamed Ayad; Rachid Bouchenna (2025). *Which Integer Divides the Reverse of Any of Its Multiples?*. DOI: [10.5281/zenodo.15283699](https://doi.org/10.5281/zenodo.15283699). URL: <https://math.colgate.edu/~integers/z37/z37.pdf>.

*Commentary.*

Ayad and Bouchenna, section 4.1, p. 8: “For every positive integer $m = a_{k}B^{k}+\cdot\cdot\cdot+a_{1}B+a_{0}$, we call the integer $m^{*}_{B} = a_{0}B^{k}+a_{1}B^{k - 1}+\cdot\cdot\cdot+a_{k}$. the reverse of $m$ in base $B$”

Here digits(B,m) is Nat.digits B m, in least-significant-first order; reverse is List.reverse and ofDigits is Nat.ofDigits. Reversing and evaluating therefore gives the displayed source expression. Trailing zeros of m become leading zeros of its reversal and contribute zero. The definition is total on natural B and m; the theorem restricts B to at least two and m to positive multiples.

**Definition 1.2 (Divisibility of every reversed multiple).**

$$\forall B \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{HasReverseMultipleProperty}\left(B, n\right) = (\forall m \in \mathbb{N},\; (0 < m) \Rightarrow ((n \mid m) \Rightarrow (n \mid \operatorname{reverseBase}\left(B, m\right))))$$

*Formalization.* `D5/S1/Digit/AyadBouchennaReverseMultipleDivisors.HasReverseMultipleProperty` (`✓ std3`).

*Citation.* Mohamed Ayad; Rachid Bouchenna (2025). *Which Integer Divides the Reverse of Any of Its Multiples?*. DOI: [10.5281/zenodo.15283699](https://doi.org/10.5281/zenodo.15283699). URL: <https://math.colgate.edu/~integers/z37/z37.pdf>.

*Commentary.*

Ayad and Bouchenna, section 4.1, p. 8: “A positive integer $n$ is said to have the property $P^{*}_{B}$ if $n$ divides $m^{*}_{B}$ for any positive multiple $m$ of $n$, that is, if for every positive integer $m$, if $n$ divides $m$, then $n$ divides $m^{*}_{B}$.”

The predicate quantifies over all natural m with 0 < m and n dividing m. Its parameters B and n are natural numbers; positivity of n and B ≥ 2 are explicit hypotheses of the characterization.

**Theorem 1.3 (The characterization in every base).**

$$\forall B \in \mathbb{N},\; (2 \le B) \Rightarrow (\forall n \in \mathbb{N},\; (0 < n) \Rightarrow (\operatorname{HasReverseMultipleProperty}\left(B, n\right) \Leftrightarrow n \mid B^{2} - 1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/AyadBouchennaReverseMultipleDivisors.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohamed Ayad; Rachid Bouchenna (2025). *Which Integer Divides the Reverse of Any of Its Multiples?*. DOI: [10.5281/zenodo.15283699](https://doi.org/10.5281/zenodo.15283699). URL: <https://math.colgate.edu/~integers/z37/z37.pdf>.

*Commentary.*

Ayad and Bouchenna, Problem 1, p. 9: “Let $B \ge 2$ be any number base. Are the divisors of $B^{2} - 1$ the only positive integers satisfying the property $P^{*}_{B}$ ?”

The answer is yes for every natural base B ≥ 2 and every positive natural n. The implication from divisibility by B² − 1 is Proposition 5 on p. 8. The converse follows by first forcing n to be coprime to B using a multiple with leading digit one. If B² is not one modulo n, the multiplicative order T of B is at least two. Sparse digit lists have ones at positions 0, 1, T, …, (c+1)T. Their forward and reversed residues force B² = 1 modulo n. The vertical bars in the statement denote divisibility; B² − 1 is natural subtraction, agreeing with integer subtraction under B ≥ 2.

## References

- Truth anchor: `D5/S1/Digit/AyadBouchennaReverseMultipleDivisors.HasReverseMultipleProperty`
- Truth anchor: `D5/S1/Digit/AyadBouchennaReverseMultipleDivisors.result`
- Truth anchor: `D5/S1/Digit/AyadBouchennaReverseMultipleDivisors.reverseBase`
