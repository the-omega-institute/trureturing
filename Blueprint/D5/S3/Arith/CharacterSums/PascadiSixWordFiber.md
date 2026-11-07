# Pascadi Six-Word Completion Fiber

## Abstract

Central six-letter returns satisfy fixed-middle compatibility equations and a finite-interval count governed by their gcd period.

Pascadi's Conjecture 6.1 predicts a uniform count for alternating T,S return words in PSL₂(Z/cZ). For c>0, units a₁,a₂ in ZMod c, and γ²=1, this module isolates the q=6 central-return equations without dividing by the possibly nonunit coefficient D. Fix h₂,h₃,h₅,h₆ in ZMod c and write D=1−a₁a₂h₂h₃ and N=c/gcd(c,D.val). For every natural H, the number of pairs (h₁,h₄) in {0,…,H−1}² whose actual sixReturnWord equals γI is at most (⌊H/N⌋+1)². The full uniform six-letter conjecture remains open.

**Definition 1.1 (returnStep).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.returnStep`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.returnStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The elementary transfer matrix T^x S used in the six-letter return word.

**Definition 1.2 (sixReturnWord).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.sixReturnWord`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.sixReturnWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The alternating six-letter product with coefficients a₁ and a₂.

**Definition 1.3 (scalarReturn).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.scalarReturn`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.scalarReturn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The central scalar matrix γI; composite moduli allow central scalars beyond ±I.

**Definition 1.4 (completionFiber).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completionFiber`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completionFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The two-coordinate completion fiber after h₂,h₃,h₅,h₆ and γ are fixed.

**Theorem 1.5 (completion_equations_of_sixReturnWord).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completion_equations_of_sixReturnWord`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completion_equations_of_sixReturnWord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

A central six-letter return forces D = γ(a₁a₂h₅h₆−1), D h₁ = γh₅−h₃, and D h₄ = γh₆−h₂. Only the assumed unit hypotheses on a₁ and a₂ are cancelled.

**Theorem 1.6 (completionFiber_period).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completionFiber_period`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completionFiber_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Two completions in one fixed-middle fiber differ by the additive order c/gcd(c,D.val) in each free coordinate. Since N divides c, the same congruence holds for arbitrary natural representatives, including representatives beyond c.

**Theorem 1.7 (sixReturnWord_fixed_middle_count).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.sixReturnWord_fixed_middle_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.sixReturnWord_fixed_middle_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Assume c>0, a₁ and a₂ are units in ZMod c, and γ²=1. Fix h₂,h₃,h₅,h₆ in ZMod c. For every H in ℕ, at most (⌊H/N⌋+1)² pairs (h₁,h₄) in {0,…,H−1}² satisfy sixReturnWord a₁ a₂ h₁ h₂ h₃ h₄ h₅ h₆ = γI, where N=c/gcd(c,(1−a₁a₂h₂h₃).val). The compatibility equations place actual solutions in the completion fiber. Its period makes the quotient map (h₁,h₄)↦(⌊h₁/N⌋,⌊h₄/N⌋) injective on those solutions; each quotient is at most ⌊H/N⌋. This includes H=0, composite moduli, and D=0, when N=1. It supplies a fixed-middle count, without estimating the sum over middle coordinates required by the full conjecture.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completionFiber`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completionFiber_period`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completion_equations_of_sixReturnWord`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.returnStep`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.scalarReturn`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.sixReturnWord`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.sixReturnWord_fixed_middle_count`
