# Thue-Morse two-block frequency

## Abstract

The Thue-Morse two-block fixed point has one-letter frequency one half.

**Definition 1.1 (The two-block substitution).**

$$\begin{aligned}\operatorname{kappaTM}:\operatorname{Bool} \to \left(\operatorname{Bool} \to \left(\operatorname{Fin}\left(3\right) \to \operatorname{Bool}\right)\right)\\\operatorname{kappaTM}\left(\operatorname{false}, \operatorname{false}\right) = ![\operatorname{false}, \operatorname{false}, \operatorname{true}]\\\operatorname{kappaTM}\left(\operatorname{false}, \operatorname{true}\right) = ![\operatorname{false}, \operatorname{true}, \operatorname{false}]\\\operatorname{kappaTM}\left(\operatorname{true}, \operatorname{false}\right) = ![\operatorname{true}, \operatorname{false}, \operatorname{true}]\\\operatorname{kappaTM}\left(\operatorname{true}, \operatorname{true}\right) = ![\operatorname{true}, \operatorname{true}, \operatorname{false}]\end{aligned}$$

*Formalization.* `D5/S1/Words/TwoBlockSubstitution/ThueMorseFrequency.kappaTM` (`✓ std3`).

*Citation.* F. M. Dekking and M. Keane (2022). *Two-block substitutions and morphic words*. DOI: [10.48550/arXiv.2202.13548](https://doi.org/10.48550/arXiv.2202.13548). URL: <https://arxiv.org/abs/2202.13548v1>.

*Commentary.*

Section 4 of v1, p. 5: “We consider the two-block substitution κTM defined by κTM(00) = 001, κTM(01) = 010, κTM(10) = 101, κTM(11) = 110.” The letters 0 and 1 are false and true. The vector notation ![a,b,c] denotes a function Fin 3 → Bool, with indices 0, 1 and 2.

**Definition 1.2 (The fixed point with prefix 00).**

$$\begin{aligned}\operatorname{tmFixed}:\mathbb{N} \to \operatorname{Bool}\\\operatorname{tmFixed}\left(0\right) = \operatorname{false}\\\operatorname{tmFixed}\left(1\right) = \operatorname{false}\\\forall n:\mathbb{N}, \operatorname{tmFixed}\left(n + 2\right) = \operatorname{ite}\left(\operatorname{Nat}.\operatorname{mod}\left(n + 2, 3\right) = 0, \operatorname{tmFixed}\left(2 \cdot \operatorname{Nat}.\operatorname{div}\left(n + 2, 3\right)\right), \operatorname{kappaTM}\left(\operatorname{tmFixed}\left(2 \cdot \operatorname{Nat}.\operatorname{div}\left(n + 2, 3\right)\right), \operatorname{tmFixed}\left(2 \cdot \operatorname{Nat}.\operatorname{div}\left(n + 2, 3\right) + 1\right), \langle\operatorname{Nat}.\operatorname{mod}\left(n + 2, 3\right)\rangle\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Words/TwoBlockSubstitution/ThueMorseFrequency.tmFixed` (`✓ std3`).

*Citation.* F. M. Dekking and M. Keane (2022). *Two-block substitutions and morphic words*. DOI: [10.48550/arXiv.2202.13548](https://doi.org/10.48550/arXiv.2202.13548). URL: <https://arxiv.org/abs/2202.13548v1>.

*Commentary.*

Section 4 of v1, p. 5: “The fixed point x = x⁽⁰⁰⁾ = x₀x₁ . . . of the two-block morphism κTM with prefix 00 satisfies very similar recurrence relations: x₃ₙ = x₂ₙ, x₃ₙ₊₁ = x₂ₙ₊₁, x₃ₙ₊₂ = 1 − x₂ₙ₊₁.” Natural indices start at zero. The well-founded recursion evaluates the residue first. Nat.div is natural integer division and Nat.mod is its remainder; ite selects its then or else branch. The angle-bracket argument is the Fin 3 index with its bound proof suppressed. The recursion yields exactly the displayed source relations, including the initial cases.

**Definition 1.3 (Dekking–Keane Conjecture 4).**

$$\operatorname{claim} \Leftrightarrow \operatorname{Filter}.\operatorname{Tendsto}\left(\operatorname{fun} N:\mathbb{N} \mapsto \frac{(\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(\operatorname{fun} n:\mathbb{N} \mapsto \operatorname{tmFixed}\left(n\right) = \operatorname{true}, \operatorname{Finset}.\operatorname{range}\left(N\right)\right)\right):\mathbb{R})}{(N:\mathbb{R})}, \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left((\frac{1}{2}:\mathbb{R})\right)\right)$$

*Formalization.* `D5/S1/Words/TwoBlockSubstitution/ThueMorseFrequency.claim` (`✓ std3`).

*Citation.* F. M. Dekking and M. Keane (2022). *Two-block substitutions and morphic words*. DOI: [10.48550/arXiv.2202.13548](https://doi.org/10.48550/arXiv.2202.13548). URL: <https://arxiv.org/abs/2202.13548v1>.

*Commentary.*

Conjecture 4 of v1, Section 4, p. 6: “The frequency of 1 in x⁽⁰⁰⁾ exists and equals ½.” The encoding counts true letters at indices n < N. Finset.filter selects those indices from Finset.range N, and Finset.card counts them. Both the cardinality and N are cast to ℝ before division; the quotient at N = 0 does not affect the limit. ArXiv v2 and the journal version change the substitution; this assertion uses the v1 table.

**Theorem 1.4 (The frequency is one half).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TwoBlockSubstitution/ThueMorseFrequency.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. M. Dekking and M. Keane (2022). *Two-block substitutions and morphic words*. DOI: [10.48550/arXiv.2202.13548](https://doi.org/10.48550/arXiv.2202.13548). URL: <https://arxiv.org/abs/2202.13548v1>.

*Commentary.*

For signs 1 − 2xₙ, one substitution step maps a pair (u,v) to (u,v,−v). After k steps, its coefficient functional is periodic modulo 2ᵏ. Multiplication by 3 permutes those residues, and the adjacent correlation sums cancel. The squared coefficient energy is 3ᵏ⁻¹ for k ≥ 1. Finite Cauchy–Schwarz bounds each aligned block sum by √(2ᵏ3ᵏ⁻¹). Splitting a prefix into aligned blocks and a bounded remainder makes the signed mean tend to zero, giving the asserted frequency.

## References

- Truth anchor: `D5/S1/Words/TwoBlockSubstitution/ThueMorseFrequency.claim`
- Truth anchor: `D5/S1/Words/TwoBlockSubstitution/ThueMorseFrequency.kappaTM`
- Truth anchor: `D5/S1/Words/TwoBlockSubstitution/ThueMorseFrequency.result`
- Truth anchor: `D5/S1/Words/TwoBlockSubstitution/ThueMorseFrequency.tmFixed`
- Dependency: [D5/S1/Recurrence/Residue/ExponentialSquareWeightTernarySupport](../../Recurrence/Residue/ExponentialSquareWeightTernarySupport.md)
