# Golden Transfer Fourfold Characterization

## Abstract

Four analytic transfer-scale conditions characterize the golden ratio.

**Theorem 1.1 (The golden transfer data agree uniquely).**

$$\left(\left(\left(\left(\operatorname{IsLUB}\left(\left\{\left(1 \le r \land r < 2\right) \land \frac{1}{2 - r} < 1 + r \mid r \in \mathbb{R}\right\}, \varphi\right) \land \varphi - 1 = \varphi^{-1}\right) \land \left(\forall x \in \mathbb{R},\; 0 < x \Rightarrow \left((y \mapsto \frac{1}{y + 1})\left(x\right) = x \Leftrightarrow x = \varphi^{-1}\right)\right)\right) \land \left|\operatorname{deriv}\left((y \mapsto \frac{1}{y + 1}), \varphi - 1\right)\right| = \varphi^{-2}\right) \land \operatorname{exp}\left(-goldenAxisTranslationLength\right) = \varphi^{-4}\right) \land \left(\forall r \in \mathbb{R},\; 1 < r \Rightarrow \left(\left(\left(\left(\operatorname{IsLUB}\left(\left\{\left(1 \le s \land s < 2\right) \land \frac{1}{2 - s} < 1 + s \mid s \in \mathbb{R}\right\}, r\right) \Leftrightarrow r = \varphi\right) \land \left((y \mapsto \frac{1}{y + 1})\left(r - 1\right) = r - 1 \Leftrightarrow r = \varphi\right)\right) \land \left(\left|\operatorname{deriv}\left((y \mapsto \frac{1}{y + 1}), r - 1\right)\right| = \varphi^{-2} \Leftrightarrow r = \varphi\right)\right) \land \left(\operatorname{exp}\left(-goldenAxisTranslationLength\right) = r^{-4} \Leftrightarrow r = \varphi\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenTransferFourfoldCharacterization.golden_transfer_fourfold_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sharp disk radius is phi, and the positive fixed point of the first inverse branch is phi minus one, equivalently phi inverse. Its local derivative has magnitude phi to the minus two, while the golden axis exponential scale is phi to the minus four.

For every candidate radius greater than one, each of the sharp-domain, fixed-point, observed-derivative, and exponential-scale conditions holds exactly when that candidate is phi.

The public theorem does not claim shortest closed-orbit minimality: the available frozen modules expose a numeric trace-three scale but no typed closed-geodesic carrier with a translation-length map.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenTransferFourfoldCharacterization.golden_transfer_fourfold_characterization`
- Dependency: [D5/S3/Analytic/Characterizations/GoldenInverseBranchFixedPoint](../../Analytic/Characterizations/GoldenInverseBranchFixedPoint.md)
- Dependency: [D5/S3/Analytic/Characterizations/GoldenTransferTriangle](../../Analytic/Characterizations/GoldenTransferTriangle.md)
- Dependency: [D5/S3/Observer/GoldenCoding/GoldenHyperbolicAxis](GoldenHyperbolicAxis.md)
