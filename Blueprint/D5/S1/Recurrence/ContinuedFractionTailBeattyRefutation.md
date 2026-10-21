# Continued-Fraction Tails and Beatty Rounding

## Abstract

Positive continued-fraction tails need not round down to their asymptotic Beatty line.

**Definition 1.1 (The asymptotic offset).**

$$\forall u \in \mathbb{N}, v \in \mathbb{R},\; \operatorname{beta}\left(u, v\right) = \frac{v \cdot \operatorname{metallicValue}\left(u\right)^{2} - \operatorname{metallicValue}\left(u\right)}{\operatorname{metallicValue}\left(u\right)^{2} + 1}$$

*Formalization.* `D5/S1/Recurrence/ContinuedFractionTailBeattyRefutation.beta` (`✓ std3`).

*Citation.* Robbert Fokkink, Gandhar Joshi (2025). *On Cloitre's hiccup sequences*. DOI: [10.1007/s11139-025-01305-1](https://doi.org/10.1007/s11139-025-01305-1). URL: <https://arxiv.org/abs/2507.16956v4>.

*Commentary.*

Section 4, page 19: “If we assume that sₙ converges to αn + β with order O(1/n), and if we take u to be a natural number, then α is the u-th metallic mean and β = (vα² − α)/(α² + 1).” Here u is natural and v is real. The metallic mean is the existing metallicValue u = (u + Real.sqrt (u² + 4))/2, with u coerced to the reals.

**Definition 1.2 (Positive tails of Equation (14)).**

$$\forall u \in \mathbb{N}, v \in \mathbb{R}, s \in \mathbb{N} \to \mathbb{R},\; (\operatorname{IsTail}\left(u, v, s\right)) \Leftrightarrow ((\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow ((0 < s\left(n\right)) \land (s\left(n\right) = (n: \mathbb{R}) \cdot (u: \mathbb{R}) + v + \frac{(n: \mathbb{R})^{2}}{s\left(n + 1\right)}))))$$

*Formalization.* `D5/S1/Recurrence/ContinuedFractionTailBeattyRefutation.IsTail` (`✓ std3`).

*Citation.* Robbert Fokkink, Gandhar Joshi (2025). *On Cloitre's hiccup sequences*. DOI: [10.1007/s11139-025-01305-1](https://doi.org/10.1007/s11139-025-01305-1). URL: <https://arxiv.org/abs/2507.16956v4>.

*Commentary.*

Section 4, page 19: “for constants u and v. Its tails satisfy sₙ = nu + v + n²/sₙ₊₁.” IsTail requires this equality and positivity at every natural index n ≥ 1. The value at zero is unrestricted; all divisions in the recurrence are real divisions.

**Definition 1.3 (The generalized rounding assertion).**

$$(claim) \Leftrightarrow ((\forall u \in \mathbb{N},\; (1 \le u) \Rightarrow (\forall v \in \mathbb{R}, s \in \mathbb{N} \to \mathbb{R},\; (\operatorname{IsTail}\left(u, v, s\right)) \Rightarrow ((\exists C \in \mathbb{R},\; \forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\left|s\left(n\right) - (\frac{(u: \mathbb{R}) + \operatorname{Real}.\operatorname{sqrt}\left((u: \mathbb{R})^{2} + 4\right)}{2} \cdot (n: \mathbb{R}) + \operatorname{beta}\left(u, v\right))\right| \le \frac{C}{(n: \mathbb{R})})) \Rightarrow (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\lfloor s\left(n\right) \rfloor = \lfloor \frac{(u: \mathbb{R}) + \operatorname{Real}.\operatorname{sqrt}\left((u: \mathbb{R})^{2} + 4\right)}{2} \cdot (n: \mathbb{R}) + \operatorname{beta}\left(u, v\right) \rfloor))))))$$

*Formalization.* `D5/S1/Recurrence/ContinuedFractionTailBeattyRefutation.claim` (`✓ std3`).

*Citation.* Robbert Fokkink, Gandhar Joshi (2025). *On Cloitre's hiccup sequences*. DOI: [10.1007/s11139-025-01305-1](https://doi.org/10.1007/s11139-025-01305-1). URL: <https://arxiv.org/abs/2507.16956v4>.

*Commentary.*

Section 4, page 19: “The generalization of Conjecture 20 then says that the rounded down tails of the continued fraction give the Beatty sequence with slope α and offset β.” Section 4, page 19: “If we assume that sₙ converges to αn + β with order O(1/n), and if we take u to be a natural number, then α is the u-th metallic mean and β = (vα² − α)/(α² + 1).” The slope is the displayed radical. The order bound means that one real constant C bounds the absolute error by C/n at every n ≥ 1. Floors take values in the integers.

**Theorem 1.4 (The generalized rounding assertion is false).**

$$\neg (\forall u \in \mathbb{N},\; (1 \le u) \Rightarrow (\forall v \in \mathbb{R}, s \in \mathbb{N} \to \mathbb{R},\; (\operatorname{IsTail}\left(u, v, s\right)) \Rightarrow ((\exists C \in \mathbb{R},\; \forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\left|s\left(n\right) - (\frac{(u: \mathbb{R}) + \operatorname{Real}.\operatorname{sqrt}\left((u: \mathbb{R})^{2} + 4\right)}{2} \cdot (n: \mathbb{R}) + \operatorname{beta}\left(u, v\right))\right| \le \frac{C}{(n: \mathbb{R})})) \Rightarrow (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\lfloor s\left(n\right) \rfloor = \lfloor \frac{(u: \mathbb{R}) + \operatorname{Real}.\operatorname{sqrt}\left((u: \mathbb{R})^{2} + 4\right)}{2} \cdot (n: \mathbb{R}) + \operatorname{beta}\left(u, v\right) \rfloor)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/ContinuedFractionTailBeattyRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/fokkink-joshi-2025-continued-fraction-tail-beatty` (refuted) by `D5/S1/Recurrence/ContinuedFractionTailBeattyRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fokkink-joshi-2025-continued-fraction-tail-beatty","declaration_gid":"D5/S1/Recurrence/ContinuedFractionTailBeattyRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Robbert Fokkink, Gandhar Joshi (2025). *On Cloitre's hiccup sequences*. DOI: [10.1007/s11139-025-01305-1](https://doi.org/10.1007/s11139-025-01305-1). URL: <https://arxiv.org/abs/2507.16956v4>.

*Commentary.*

For u = 2 and v = 1, the slope is 1 + Real.sqrt 2 and beta 2 1 = 1/2. A contraction on a closed set of bounded continuous functions constructs positive tails whose error lies strictly between 1/(8n) and metallicValue 2/(4n). At n = 1 the Beatty line has floor 2, while the recurrence gives s 1 = 3 + 1/(s 2) > 3. Thus their floors differ. The assertion quantified over Pell indices, uniqueness of positive tails, and convergence of finite continued-fraction truncations are not proved here.

## References

- Truth anchor: `D5/S1/Recurrence/ContinuedFractionTailBeattyRefutation.IsTail`
- Truth anchor: `D5/S1/Recurrence/ContinuedFractionTailBeattyRefutation.beta`
- Truth anchor: `D5/S1/Recurrence/ContinuedFractionTailBeattyRefutation.claim`
- Truth anchor: `D5/S1/Recurrence/ContinuedFractionTailBeattyRefutation.result`
- Dependency: [D5/S0/Asymptotics/MetallicFamily](../../S0/Asymptotics/MetallicFamily.md)
- Dependency: [D5/S0/Asymptotics/MetallicMinimum](../../S0/Asymptotics/MetallicMinimum.md)
