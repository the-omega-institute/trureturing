# Robustness of ancilla-free testers

## Abstract

Ancilla-free testers with a common normalization state have the robustness of their canonical POVMs.

**Definition 1.1 (Quantum testers).**

$$\forall (y: \operatorname{Type}), (\forall (x: \operatorname{Type}), (\forall (j: \operatorname{Type}), ([\operatorname{Fintype}\left(y\right)], ([\operatorname{DecidableEq}\left(y\right)], ([\operatorname{Fintype}\left(x\right)], ([\operatorname{Fintype}\left(j\right)], (\forall (t: (j) \to (\operatorname{Matrix}\left((y \times x), (y \times x), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.IsTester}\left(t\right)) \Leftrightarrow ((\forall (a: j), (\operatorname{Matrix.PosSemidef}\left(t\left(a\right)\right))) \land (\exists (\sigma: \operatorname{Matrix}\left(x, x, \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\sigma\right)) \land (\sum_{a: j} (t\left(a\right)) = \operatorname{Matrix.kronecker}\left((1: \operatorname{Matrix}\left(y, y, \mathbb{C}\right)), \sigma\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.IsTester` (`✓ std3`).

*Citation.* Michal Sedlák; Daniel Reitzner; Giulio Chiribella; Mário Ziman (2016). *Incompatible measurements on quantum causal networks*. DOI: [10.1103/PhysRevA.93.052323](https://doi.org/10.1103/PhysRevA.93.052323). URL: <https://arxiv.org/abs/1511.00976v2>.

*Commentary.*

A tester is a finite family t of positive semidefinite effects on the output-input tensor product. Its sum is the output identity tensored with a density matrix σ on the input. Here IsDensity means positive semidefinite with complex trace equal to one. This is the tester definition in ti_pra_07.tex, lines 247–259.

**Definition 1.2 (Compatibility after adding tester noise).**

$$\forall (y: \operatorname{Type}), (\forall (x: \operatorname{Type}), (\forall (j: \operatorname{Type}), (\forall (k: \operatorname{Type}), ([\operatorname{Fintype}\left(y\right)], ([\operatorname{DecidableEq}\left(y\right)], ([\operatorname{Fintype}\left(x\right)], ([\operatorname{Fintype}\left(j\right)], ([\operatorname{Fintype}\left(k\right)], (\forall (lam: \mathbb{R}), (\forall (a: (j) \to (\operatorname{Matrix}\left((y \times x), (y \times x), \mathbb{C}\right))), (\forall (b: (k) \to (\operatorname{Matrix}\left((y \times x), (y \times x), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.TesterCompatibleAt}\left(lam, a, b\right)) \Leftrightarrow (\exists (e: (j) \to (\operatorname{Matrix}\left((y \times x), (y \times x), \mathbb{C}\right))), (\exists (f: (k) \to (\operatorname{Matrix}\left((y \times x), (y \times x), \mathbb{C}\right))), (\exists (c: ((j \times k)) \to (\operatorname{Matrix}\left((y \times x), (y \times x), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.IsTester}\left(e\right)) \land ((\operatorname{D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.IsTester}\left(f\right)) \land ((\operatorname{D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.IsTester}\left(c\right)) \land ((\forall (u: j), (\sum_{v: k} (c\left((u, v)\right)) = \operatorname{HSMul.hSMul}\left((1: \mathbb{R}) - lam, a\left(u\right)\right) + \operatorname{HSMul.hSMul}\left(lam, e\left(u\right)\right))) \land (\forall (v: k), (\sum_{u: j} (c\left((u, v)\right)) = \operatorname{HSMul.hSMul}\left((1: \mathbb{R}) - lam, b\left(v\right)\right) + \operatorname{HSMul.hSMul}\left(lam, f\left(v\right)\right))))))))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.TesterCompatibleAt` (`✓ std3`).

*Citation.* Michal Sedlák; Daniel Reitzner; Giulio Chiribella; Mário Ziman (2016). *Incompatible measurements on quantum causal networks*. DOI: [10.1103/PhysRevA.93.052323](https://doi.org/10.1103/PhysRevA.93.052323). URL: <https://arxiv.org/abs/1511.00976v2>.

*Commentary.*

The noise testers e and f have the outcome types of a and b. A joint tester c has outcomes j × k, and its marginals are the two mixtures at the same real weight lam. The three testers may have different normalization states, and the noise need not be ancilla-free. The predicate itself allows every real lam; robustness restricts lam to the unit interval. These are the marginal and noise conditions in ti_pra_07.tex, lines 451–459 and 567–570.

**Definition 1.3 (Tester robustness).**

$$\forall (y: \operatorname{Type}), (\forall (x: \operatorname{Type}), (\forall (j: \operatorname{Type}), (\forall (k: \operatorname{Type}), ([\operatorname{Fintype}\left(y\right)], ([\operatorname{DecidableEq}\left(y\right)], ([\operatorname{Fintype}\left(x\right)], ([\operatorname{Fintype}\left(j\right)], ([\operatorname{Fintype}\left(k\right)], (\forall (a: (j) \to (\operatorname{Matrix}\left((y \times x), (y \times x), \mathbb{C}\right))), (\forall (b: (k) \to (\operatorname{Matrix}\left((y \times x), (y \times x), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.testerRobustness}\left(a, b\right): \mathbb{R}) = \operatorname{sInf}\left(\{(lam: \mathbb{R}) \mid ((0: \mathbb{R}) \le lam) \land ((lam \le (1: \mathbb{R})) \land (\operatorname{D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.TesterCompatibleAt}\left(lam, a, b\right)))\}\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.testerRobustness` (`✓ std3`).

*Citation.* Michal Sedlák; Daniel Reitzner; Giulio Chiribella; Mário Ziman (2016). *Incompatible measurements on quantum causal networks*. DOI: [10.1103/PhysRevA.93.052323](https://doi.org/10.1103/PhysRevA.93.052323). URL: <https://arxiv.org/abs/1511.00976v2>.

*Commentary.*

Tester robustness is the infimum of the real weights in the closed unit interval for which separate tester noises give compatible mixtures. The source uses a minimum in ti_pra_07.tex, lines 574–577; this infimum formulation makes no assertion of attainment.

**Definition 1.4 (Compatibility after adding measurement noise).**

$$\forall (z: \operatorname{Type}), (\forall (j: \operatorname{Type}), (\forall (k: \operatorname{Type}), ([\operatorname{Fintype}\left(z\right)], ([\operatorname{DecidableEq}\left(z\right)], ([\operatorname{Fintype}\left(j\right)], ([\operatorname{Fintype}\left(k\right)], (\forall (lam: \mathbb{R}), (\forall (p: (j) \to (\operatorname{Matrix}\left(z, z, \mathbb{C}\right))), (\forall (q: (k) \to (\operatorname{Matrix}\left(z, z, \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.POVMCompatibleAt}\left(lam, p, q\right)) \Leftrightarrow (\exists (u: (j) \to (\operatorname{Matrix}\left(z, z, \mathbb{C}\right))), (\exists (v: (k) \to (\operatorname{Matrix}\left(z, z, \mathbb{C}\right))), (\exists (g: ((j \times k)) \to (\operatorname{Matrix}\left(z, z, \mathbb{C}\right))), (((\forall (a: j), (\operatorname{Matrix.PosSemidef}\left(u\left(a\right)\right))) \land (\sum_{a: j} (u\left(a\right)) = (1: \operatorname{Matrix}\left(z, z, \mathbb{C}\right)))) \land (((\forall (b: k), (\operatorname{Matrix.PosSemidef}\left(v\left(b\right)\right))) \land (\sum_{b: k} (v\left(b\right)) = (1: \operatorname{Matrix}\left(z, z, \mathbb{C}\right)))) \land (((\forall (ab: (j \times k)), (\operatorname{Matrix.PosSemidef}\left(g\left(ab\right)\right))) \land (\sum_{ab: (j \times k)} (g\left(ab\right)) = (1: \operatorname{Matrix}\left(z, z, \mathbb{C}\right)))) \land ((\forall (a: j), (\sum_{b: k} (g\left((a, b)\right)) = \operatorname{HSMul.hSMul}\left((1: \mathbb{R}) - lam, p\left(a\right)\right) + \operatorname{HSMul.hSMul}\left(lam, u\left(a\right)\right))) \land (\forall (b: k), (\sum_{a: j} (g\left((a, b)\right)) = \operatorname{HSMul.hSMul}\left((1: \mathbb{R}) - lam, q\left(b\right)\right) + \operatorname{HSMul.hSMul}\left(lam, v\left(b\right)\right))))))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.POVMCompatibleAt` (`✓ std3`).

*Citation.* Michal Sedlák; Daniel Reitzner; Giulio Chiribella; Mário Ziman (2016). *Incompatible measurements on quantum causal networks*. DOI: [10.1103/PhysRevA.93.052323](https://doi.org/10.1103/PhysRevA.93.052323). URL: <https://arxiv.org/abs/1511.00976v2>.

*Commentary.*

The families u, v and g are POVMs: every effect is positive semidefinite and each whole family sums to the identity. The two marginals of g are the mixtures of p and q with the separate noises u and v. All scalar actions in these formulas use real scalars on complex matrices. The measurement noise condition is stated in ti_pra_07.tex, lines 761–765.

**Definition 1.5 (Measurement robustness).**

$$\forall (z: \operatorname{Type}), (\forall (j: \operatorname{Type}), (\forall (k: \operatorname{Type}), ([\operatorname{Fintype}\left(z\right)], ([\operatorname{DecidableEq}\left(z\right)], ([\operatorname{Fintype}\left(j\right)], ([\operatorname{Fintype}\left(k\right)], (\forall (p: (j) \to (\operatorname{Matrix}\left(z, z, \mathbb{C}\right))), (\forall (q: (k) \to (\operatorname{Matrix}\left(z, z, \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.povmRobustness}\left(p, q\right): \mathbb{R}) = \operatorname{sInf}\left(\{(lam: \mathbb{R}) \mid ((0: \mathbb{R}) \le lam) \land ((lam \le (1: \mathbb{R})) \land (\operatorname{D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.POVMCompatibleAt}\left(lam, p, q\right)))\}\right))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.povmRobustness` (`✓ std3`).

*Citation.* Michal Sedlák; Daniel Reitzner; Giulio Chiribella; Mário Ziman (2016). *Incompatible measurements on quantum causal networks*. DOI: [10.1103/PhysRevA.93.052323](https://doi.org/10.1103/PhysRevA.93.052323). URL: <https://arxiv.org/abs/1511.00976v2>.

*Commentary.*

Measurement robustness is the infimum of the weights in the closed unit interval that permit a joint POVM after adding separate noise POVMs. It expresses the robustness of ti_pra_07.tex, lines 767–770, using an infimum without asserting attainment.

**Definition 1.6 (Equality for a common ancilla-free state).**

$$(\operatorname{D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.claim}) \Leftrightarrow (\forall (y: \operatorname{Type}), (\forall (x: \operatorname{Type}), (\forall (j: \operatorname{Type}), (\forall (k: \operatorname{Type}), ([\operatorname{Fintype}\left(y\right)], ([\operatorname{DecidableEq}\left(y\right)], ([\operatorname{Fintype}\left(x\right)], ([\operatorname{DecidableEq}\left(x\right)], ([\operatorname{Fintype}\left(j\right)], ([\operatorname{DecidableEq}\left(j\right)], ([\operatorname{Fintype}\left(k\right)], ([\operatorname{DecidableEq}\left(k\right)], (\forall (\rho: \operatorname{Matrix}\left(x, x, \mathbb{C}\right)), (\forall (m: (j) \to (\operatorname{Matrix}\left(y, y, \mathbb{C}\right))), (\forall (n: (k) \to (\operatorname{Matrix}\left(y, y, \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)) \to (((\forall (a: j), (\operatorname{Matrix.PosSemidef}\left(m\left(a\right)\right))) \land (\sum_{a: j} (m\left(a\right)) = (1: \operatorname{Matrix}\left(y, y, \mathbb{C}\right)))) \to (((\forall (b: k), (\operatorname{Matrix.PosSemidef}\left(n\left(b\right)\right))) \land (\sum_{b: k} (n\left(b\right)) = (1: \operatorname{Matrix}\left(y, y, \mathbb{C}\right)))) \to (\operatorname{D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.testerRobustness}\left((\lambda (a: j) \mapsto (\operatorname{Matrix.kronecker}\left(m\left(a\right), \rho\right))), (\lambda (b: k) \mapsto (\operatorname{Matrix.kronecker}\left(n\left(b\right), \rho\right)))\right) = \operatorname{D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.povmRobustness}\left((\lambda (a: j) \mapsto (\operatorname{Matrix.kronecker}\left(m\left(a\right), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(\operatorname{Matrix.rank}\left(\rho\right)\right), \operatorname{Fin}\left(\operatorname{Matrix.rank}\left(\rho\right)\right), \mathbb{C}\right))\right))), (\lambda (b: k) \mapsto (\operatorname{Matrix.kronecker}\left(n\left(b\right), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(\operatorname{Matrix.rank}\left(\rho\right)\right), \operatorname{Fin}\left(\operatorname{Matrix.rank}\left(\rho\right)\right), \mathbb{C}\right))\right)))\right))))))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michal Sedlák; Daniel Reitzner; Giulio Chiribella; Mário Ziman (2016). *Incompatible measurements on quantum causal networks*. DOI: [10.1103/PhysRevA.93.052323](https://doi.org/10.1103/PhysRevA.93.052323). URL: <https://arxiv.org/abs/1511.00976v2>.

*Commentary.*

For arbitrary finite output and input types y and x and outcome types j and k, take a common density matrix ρ and output POVMs m and n. Their ancilla-free testers have effects m(a) ⊗ ρ and n(b) ⊗ ρ. The associated canonical POVMs have effects m(a) ⊗ I and n(b) ⊗ I on y × Fin(rank ρ), using coordinates on the support of ρ. The equality concerns precisely these two robustness values. The product characterization is Proposition 3, ti_pra_07.tex, lines 333–338; the canonical POVM is defined at lines 281–303. The common-state setting appears at line 772 and the ancilla-free question at line 807.

**Theorem 1.7 (Equality of tester and canonical measurement robustness).**

$$\forall (y: \operatorname{Type}), (\forall (x: \operatorname{Type}), (\forall (j: \operatorname{Type}), (\forall (k: \operatorname{Type}), ([\operatorname{Fintype}\left(y\right)], ([\operatorname{DecidableEq}\left(y\right)], ([\operatorname{Fintype}\left(x\right)], ([\operatorname{DecidableEq}\left(x\right)], ([\operatorname{Fintype}\left(j\right)], ([\operatorname{DecidableEq}\left(j\right)], ([\operatorname{Fintype}\left(k\right)], ([\operatorname{DecidableEq}\left(k\right)], (\forall (\rho: \operatorname{Matrix}\left(x, x, \mathbb{C}\right)), (\forall (m: (j) \to (\operatorname{Matrix}\left(y, y, \mathbb{C}\right))), (\forall (n: (k) \to (\operatorname{Matrix}\left(y, y, \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)) \to (((\forall (a: j), (\operatorname{Matrix.PosSemidef}\left(m\left(a\right)\right))) \land (\sum_{a: j} (m\left(a\right)) = (1: \operatorname{Matrix}\left(y, y, \mathbb{C}\right)))) \to (((\forall (b: k), (\operatorname{Matrix.PosSemidef}\left(n\left(b\right)\right))) \land (\sum_{b: k} (n\left(b\right)) = (1: \operatorname{Matrix}\left(y, y, \mathbb{C}\right)))) \to (\operatorname{D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.testerRobustness}\left((\lambda (a: j) \mapsto (\operatorname{Matrix.kronecker}\left(m\left(a\right), \rho\right))), (\lambda (b: k) \mapsto (\operatorname{Matrix.kronecker}\left(n\left(b\right), \rho\right)))\right) = \operatorname{D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.povmRobustness}\left((\lambda (a: j) \mapsto (\operatorname{Matrix.kronecker}\left(m\left(a\right), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(\operatorname{Matrix.rank}\left(\rho\right)\right), \operatorname{Fin}\left(\operatorname{Matrix.rank}\left(\rho\right)\right), \mathbb{C}\right))\right))), (\lambda (b: k) \mapsto (\operatorname{Matrix.kronecker}\left(n\left(b\right), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(\operatorname{Matrix.rank}\left(\rho\right)\right), \operatorname{Fin}\left(\operatorname{Matrix.rank}\left(\rho\right)\right), \mathbb{C}\right))\right)))\right)))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.result` (`✓ std3`). ∎

*Resolves.* `Problems/sedlak-reitzner-chiribella-ziman-2016-ancilla-free-tester-robustness` (proved) by `D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sedlak-reitzner-chiribella-ziman-2016-ancilla-free-tester-robustness","declaration_gid":"D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Michal Sedlák; Daniel Reitzner; Giulio Chiribella; Mário Ziman (2016). *Incompatible measurements on quantum causal networks*. DOI: [10.1103/PhysRevA.93.052323](https://doi.org/10.1103/PhysRevA.93.052323). URL: <https://arxiv.org/abs/1511.00976v2>.

*Commentary.*

First, tensoring each effect of a POVM with ρ gives a tester: Kronecker products preserve positive semidefiniteness, and the effects sum to I ⊗ ρ. Conversely, take the partial trace over x of each tester effect. This preserves positive semidefiniteness and finite sums. A tester normalized by any density matrix σ is sent to a POVM because the partial trace of I ⊗ σ is (tr σ)I = I.

For a fixed lam, suppose u, v and g are noise and joint POVMs for m and n. Tensor all three families with ρ. Distributing the Kronecker product over the marginal sums, addition and real scalar multiplication gives noise and joint testers for m ⊗ ρ and n ⊗ ρ. In the reverse direction, start with arbitrary noise testers e and f and a joint tester c. Apply the partial trace over x to all three families and their marginal equations. They become POVMs, and tr ρ = 1 sends m(a) ⊗ ρ to m(a) and n(b) ⊗ ρ to n(b). Thus compatibility at lam is equivalent for the product testers and the output POVMs, even when e, f and c have different normalization states.

Next tensor noise and joint POVMs with the identity on Fin r. Positivity, unit normalization and the marginal equations are preserved. For the reverse direction assume 0 < r and compress every effect to the principal submatrix indexed by pairs (b,0). Principal submatrices preserve positivity. The inclusion b ↦ (b,0) is injective, so compression preserves the identity, and it commutes with finite sums, addition and real scalar multiplication. The compressed entries of t ⊗ I are exactly the entries of t. Consequently compression turns noise and joint POVMs on y × Fin r into noise and joint POVMs on y with the required marginals.

The trace equation tr ρ = 1 implies ρ ≠ 0, hence some column has a nonzero entry. The span of the columns therefore has positive dimension, giving 0 < rank ρ. The first pair of implications identifies the feasible weights in [0,1] for the product testers with those for m and n. The tensor and compression implications identify the latter set with the feasible weights for the canonical POVMs when r = rank ρ. Composing these set equalities and taking infima proves the displayed equality. No minimizer or numerical robustness value is needed.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.IsTester`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.POVMCompatibleAt`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.TesterCompatibleAt`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.povmRobustness`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.testerRobustness`
- Dependency: [D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction](../Divergence/ConditionalHockeyStickOrthogonalReduction.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](../Information/SLDSpectralEnergy.md)
