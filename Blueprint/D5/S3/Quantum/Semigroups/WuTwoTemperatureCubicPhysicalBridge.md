# Physical two-temperature cubic bridge

## Abstract

The physical two-temperature cubic Gibbs bridge for two CAR modes.

In occupation order 00, 01, 10, 11, the left mode has ratio r and the right mode has ratio R. The one-mode entries are a(t) = 1/(1+t^3) and b(t) = t^3/(1+t^3), so the product Gibbs matrix is D(R,r) = d(r) ⊗ₖ d(R), with diagonal entry D_o,o = localEntry(r,o.1) localEntry(R,o.2).

The positive diagonal root G has entry rootEntry(R,r,o) = localRoot(r,o.1) localRoot(R,o.2), where localRoot(t,0) = a(t)^(1/6) and localRoot(t,1) = a(t)^(1/6) √t. Thus G^6 = D, G is the real continuous-functional-calculus sixth root of D, and G GInv = GInv G = I.

**Theorem 1.1 (Matrix jump/Gibbs intertwining).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicPhysicalBridge.jump_mul_G`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicPhysicalBridge.jump_mul_G` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For j in the right-then-left mode order, modeRatio(R,r,j) is R or r. The directed lowering jump satisfies J_j G = √modeRatio(R,r,j) · G J_j, and the adjoint satisfies G J_jᴴ = √modeRatio(R,r,j) · J_jᴴ G. These are the actual matrix identities used by the sandwich.

**Theorem 1.2 (Cold plus tracial generator).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicPhysicalBridge.generator_eq_cold_add_tracial`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicPhysicalBridge.generator_eq_cold_add_tracial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

At spectator ratio 1, the rates 2a(1) and 2b(1) are both 1. Hence generator(R,1,X) is modeGenerator(R,J₀,X) plus the tracial second-mode dissipator.

**Theorem 1.3 (Physical mode trace).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicPhysicalBridge.mode_energy_eq_operator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicPhysicalBridge.mode_energy_eq_operator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For M = U diag(v) Uᴴ and X = GInv M GInv, the Gibbs-sandwiched operator trace equals the directed energy sum. Each cell is cost(t,x,y) = γ(t)(t x − y)^2(t x + y), weighted by |(Uᴴ J_j U)ᵢₖ|².

**Theorem 1.4 (Ordinary Wu cubic trace).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicPhysicalBridge.energy_eq_operator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicPhysicalBridge.energy_eq_operator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Summing the right and left mode identities gives energy(R,U,0,v) + energy(r,U,1,v) = (9/8) Re Tr(M² G generator(R,r,GInv M GInv) G). The equality holds for arbitrary real spectral roots, including zero roots.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicPhysicalBridge.energy_eq_operator`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicPhysicalBridge.generator_eq_cold_add_tracial`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicPhysicalBridge.jump_mul_G`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicPhysicalBridge.mode_energy_eq_operator`
- Dependency: [D5/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker](WuTwoModeCliffordPluecker.md)
