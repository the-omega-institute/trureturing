# Pascadi Six-Word Completion Fiber

## Abstract

A fixed-middle six-letter PSL₂ return fiber is forced by entrywise compatibility equations and has a gcd-periodic completion coordinate.

Pascadi's Conjecture 6.1 predicts a uniform count for alternating T,S return words in PSL₂(Z/cZ). This module isolates the q=6 central-return equations without dividing by the possibly nonunit coefficient D.

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

Two completions in one fixed-middle fiber differ by the additive order c/gcd(c,D.val) in each free coordinate. This is the gcd-periodic stratum needed for a bounded representative count.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completionFiber`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completionFiber_period`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completion_equations_of_sixReturnWord`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.returnStep`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.scalarReturn`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSixWordFiber.sixReturnWord`
