# Golden Carrier Foundations

## Abstract

Frozen proofs assemble conjugation, norm, units, and unique factorization.

**Theorem 1.1 (Conjugation, norm, units, and factorization of the golden carrier).**

$$\exists\,\sigma\in\operatorname{Aut}(\mathcal{O}_\varphi):\ \sigma=\overline{(\,\cdot\,)},\ \sigma^{2}=\mathrm{id};\quad N(xy)=N(x)\,N(y);\quad \mathcal{O}_\varphi^{\times}=\{\pm\varphi^{n}\mid n\in\mathbb{Z}\},\ N(\varphi)=-1;\quad \mathcal{O}_\varphi\ \text{is a PID and a UFD.}$$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/CarrierFoundations.golden_carrier_foundations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The golden integer carrier admits a ring automorphism that agrees pointwise with conjugation and is involutive. The integer norm is multiplicative. An element is a unit exactly when it is a signed integral power of the golden ratio, whose norm is minus one. The carrier is a principal ideal ring and a unique factorization monoid.

The statement is assembly-only: each clause is witnessed by its frozen proof — the conjugation equivalence, norm multiplicativity, the signed-power unit classification, and the principal-ideal and unique-factorization instances — so the theorem packages the four foundations behind a single declaration without re-proving any of them.

## References

- Truth anchor: `D5/S1/Scale/CarrierFoundations.golden_carrier_foundations`
- Dependency: [D5/S0/Carrier/Norm](../../S0/Carrier/Norm.md)
