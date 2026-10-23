# Feasible spectral perturbation

## Abstract

Seven spectral levels admit a nonzero trace-zero perturbation preserving both positive pencils for a positive radius.

**Theorem 1.1 (A positive feasible radius).**

$$\forall (l:Fin\left(9\right)\to \mathbb{R}), ((Antitone\left(l\right))\land (\forall (i:Fin\left(9\right)), 0\leq l\left(i\right))\land (\sum_{i:Fin\left(9\right)} l\left(i\right)=1)\land ((K1\left(l\right)).PosSemidef)\land ((K2\left(l\right)).PosSemidef)\land (7\leq (Set.range\left(l\right)).ncard))\Rightarrow (\exists (v:Fin\left(9\right)\to \mathbb{R}), (v\neq 0)\land (\exists (r:\mathbb{R}), (0<r)\land (\forall (t:\mathbb{R}), (abs\left(t\right)<r)\Rightarrow ((Antitone\left(l+HSMul.hSMul\left(t, v\right)\right))\land (\forall (i:Fin\left(9\right)), 0\leq (l+HSMul.hSMul\left(t, v\right))\left(i\right))\land (\sum_{i:Fin\left(9\right)} (l+HSMul.hSMul\left(t, v\right))\left(i\right)=1)\land ((K1\left(l+HSMul.hSMul\left(t, v\right)\right)).PosSemidef)\land ((K2\left(l+HSMul.hSMul\left(t, v\right)\right)).PosSemidef)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralFeasiblePerturbation.spectral_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Seven distinct levels give a nonzero block-preserving trace-zero direction. The dependency between the two pencil kernel equations leaves at most six independent constraints. Positive leading minors and continuity give a radius preserving positive semidefiniteness, order, nonnegativity, and mass.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralFeasiblePerturbation.spectral_radius`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSixLevelExtremality](QutritSixLevelExtremality.md)
