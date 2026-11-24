# Square-root limits for the nonprime Mangoldt contribution

## Abstract

The mod-four square-layer correction

For a real cutoff x, HChi(x) sums Λ(n)χ₄(n) over the nonprime positive integers at most x. The character χ₄ takes values 0 on even integers, 1 on the residue class 1, and −1 on the residue class 3 modulo four.

**Theorem 1.1 (The nonprime Mangoldt sum).**

$$\lim_{x\to +\infty} \frac{\operatorname{HChi}\left(x\right)}{\sqrt{x}} = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletRampPrimeTail.HChi_root_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every odd prime square has character value 1, and the square of 2 has character value 0. For x ≥ 4, the weighted square layer is θ(√x) − log 2. The absolute remainder is bounded by ψ(x) − θ(x) − θ(√x). After division by √x, the remainder tends to zero and θ(√x)/√x tends to one.

**Theorem 1.2 (The integrated ramp correction).**

$$\lim_{x\to +\infty} \frac{x\,\int_{t>x} \frac{\operatorname{HChi}\left(t\right)}{t^{2}}\,d t}{\sqrt{x}} = 2$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletRampPrimeTail.HChi_ramp_tail_root_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral uses Lebesgue measure over t > x. The bound |HChi(t)| ≤ ψ(t) − θ(t) gives an integrable majorant after division by t² on t > 1. The first limit bounds HChi(t) between arbitrarily close multiples of √t on a sufficiently far tail. Integrating √t/t² over t > x gives 2/√x.

## References

- Truth anchor: `D5/S3/CharacterSums/DirichletRampPrimeTail.HChi_ramp_tail_root_limit`
- Truth anchor: `D5/S3/CharacterSums/DirichletRampPrimeTail.HChi_root_limit`
- Dependency: [D5/S3/Arith/Robin/EulerLayerRootCorrection](../Arith/Robin/EulerLayerRootCorrection.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection](../Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection.md)
