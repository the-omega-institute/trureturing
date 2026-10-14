# The Haar mean of non-local nonstabilizerness

## Abstract

The Appendix C density has integrable first moment 10/3 minus pi.

**Definition 1.1 (The square root in the density).**

$$\forall y \in \mathbb{R},\; \operatorname{D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean.zC}\left(y\right) = \operatorname{Real.sqrt}\left(4 - 3 \cdot \operatorname{Real.exp}\left(y\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean.zC` (`✓ std3`).

*Citation.* Dongheng Qian; Jing Wang (2025). *Quantum non-local nonstabilizerness*. DOI: [10.1103/PhysRevA.111.052443](https://doi.org/10.1103/PhysRevA.111.052443). URL: <https://arxiv.org/abs/2502.06393v4>.

*Commentary.*

Appendix C introduces z = √(4 − 3e^y) in (C5). This real-valued function is defined for every real y using the real square root.

**Definition 1.2 (The Appendix C density).**

$$\forall y \in \mathbb{R},\; \operatorname{D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean.nnDensity}\left(y\right) = (\text{if} ((0 < y) \land (y < \operatorname{Real.log}\left(\frac{4}{3}\right))) \text{then} \frac{3 \cdot \operatorname{Real.exp}\left(\frac{-y}{2}\right)}{4 \cdot \operatorname{D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean.zC}\left(y\right) \cdot \operatorname{Real.sqrt}\left(2 \cdot (\operatorname{Real.exp}\left(y\right) - 1)\right)} \cdot ((\operatorname{Real.exp}\left(\frac{y}{2}\right) + \operatorname{D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean.zC}\left(y\right)) \cdot \operatorname{Real.sqrt}\left(1 - \operatorname{Real.exp}\left(\frac{-y}{2}\right) \cdot \operatorname{D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean.zC}\left(y\right)\right) + (\operatorname{Real.exp}\left(\frac{y}{2}\right) - \operatorname{D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean.zC}\left(y\right)) \cdot \operatorname{Real.sqrt}\left(1 + \operatorname{Real.exp}\left(\frac{-y}{2}\right) \cdot \operatorname{D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean.zC}\left(y\right)\right)) \text{else} 0)$$

*Formalization.* `D5/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean.nnDensity` (`✓ std3`).

*Citation.* Dongheng Qian; Jing Wang (2025). *Quantum non-local nonstabilizerness*. DOI: [10.1103/PhysRevA.111.052443](https://doi.org/10.1103/PhysRevA.111.052443). URL: <https://arxiv.org/abs/2502.06393v4>.

*Commentary.*

Equation (C5) gives the density of y = M(x) for a Haar-random two-qubit pure state. The formula is used on 0 < y < ln(4/3), and the function is zero everywhere else, including both endpoints. Every exponential and square root is real.

**Definition 1.3 (Integrability and the exact first moment).**

$$\operatorname{D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean.claim} \Leftrightarrow ((\operatorname{MeasureTheory.Integrable}\left((\text{fun} (y: \mathbb{R}) \mapsto y \cdot \operatorname{D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean.nnDensity}\left(y\right))\right)) \land (\int y: \mathbb{R}, (y \cdot \operatorname{D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean.nnDensity}\left(y\right)) = \frac{10}{3} - \operatorname{Real.pi}))$$

*Formalization.* `D5/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dongheng Qian; Jing Wang (2025). *Quantum non-local nonstabilizerness*. DOI: [10.1103/PhysRevA.111.052443](https://doi.org/10.1103/PhysRevA.111.052443). URL: <https://arxiv.org/abs/2502.06393v4>.

*Commentary.*

The source asks in §III and Appendix C for a closed form of the mean ȳ ≡ ∫ yP(y)dy, with P given by (C5). The statement combines integrability of the first-moment function on the real line with the value 10/3 − π of its Lebesgue integral, taken with respect to volume. Through the substitution t = 1 − 2x, this mean equals ∫₀¹ M(x)·3(1 − 2x)² dx, the Haar average under (C1) and the source's Schmidt-weight density P(x) = 3(1 − 2x)². This equivalence is mathematical background and is not part of the formal statement.

**Theorem 1.4 (The first moment is 10/3 minus pi).**

$$\operatorname{D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean.result` (`✓ std3`). ∎

*Resolves.* `Problems/qian-wang-2025-nonlocal-nonstabilizerness-haar-mean` (proved) by `D5/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"qian-wang-2025-nonlocal-nonstabilizerness-haar-mean","declaration_gid":"D5/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Dongheng Qian; Jing Wang (2025). *Quantum non-local nonstabilizerness*. DOI: [10.1103/PhysRevA.111.052443](https://doi.org/10.1103/PhysRevA.111.052443). URL: <https://arxiv.org/abs/2502.06393v4>.

*Commentary.*

Put a = ln(4/3). The primitive F(t) = −t³ ln(t⁴ − t² + 1) + (4/3)t³ + 2t − 2(arctan(2t + √3) + arctan(2t − √3)) has derivative −3t² ln(t⁴ − t² + 1), with F(0) = 0 and F(1) = 10/3 − π. The last endpoint value follows from (2 + √3)(2 − √3) = 1 and the reciprocal identity for the real arctangent.

For 0 < y < a, set w = √(4e^(−y) − 3) and t₋ = √((1 − w)/2), t₊ = √((1 + w)/2). Both branches satisfy t⁴ − t² + 1 = e^(−y), and (C5) becomes 3e^(−y)(t₋ + t₊)/(2w). Thus G(y) = F(t₋(y)) − F(t₊(y)) has derivative yP(y). Its endpoint values are G(0) = −(10/3 − π) and G(a) = 0.

On this interval, 0 ≤ yP(y) ≤ a√3/√(a − y). The majorant is integrable because its endpoint singularity has exponent −1/2. The fundamental theorem of calculus gives the first moment as G(a) − G(0) = 10/3 − π. The integrand vanishes outside the interval, so integrability and the same integral value hold on the whole real line.

## References

- Truth anchor: `D5/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean.claim`
- Truth anchor: `D5/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean.nnDensity`
- Truth anchor: `D5/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean.result`
- Truth anchor: `D5/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean.zC`
