# CycleTwentyOneNoUniformMixing

## Abstract

Orbit sums, support masks and an exact integer Laurent identity exclude instantaneous uniform mixing on the cycle with twenty-one vertices.

**Theorem 1.1 (no_uniform_mixing_of_no_common_nonzero_root).**

$$\forall (\operatorname{t} : \mathbb{R}) , (\forall (\operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} : \mathbb{C}) , \operatorname{x0} \neq 0 \to \operatorname{x1} \neq 0 \to \operatorname{x2} \neq 0 \to \operatorname{x3} \neq 0 \to \operatorname{x4} \neq 0 \to \operatorname{x5} \neq 0 \to \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g1} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = 0 \to \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g2} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = 0 \to \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g3} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = 0 \to \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g4} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = 0 \to \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g5} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = 0 \to \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g6} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = 0 \to \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g7} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = 0 \to \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g8} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = 0 \to \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g9} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = 0 \to \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g10} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = 0 \to \operatorname{False}) \to (\neg (\forall \operatorname{a} \operatorname{b} : \operatorname{ZMod} 21 , \operatorname{Complex.normSq} (\operatorname{NormedSpace.exp} (\operatorname{SMul.smul} (((\operatorname{t} : \mathbb{C}) \cdot \operatorname{Complex.I})) (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Fourier.cycleA})) \operatorname{a} \operatorname{b}) = 1 / 21))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/CycleTwentyOneNoUniformMixing.no_uniform_mixing_of_no_common_nonzero_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the ten cleared phase equations have no common nonzero complex root, the Fourier correlations prevent uniform mixing on C21. The six actual exponential phases are nonzero and obey all ten equations whenever uniform mixing holds.

**Definition 1.2 (claim).**

$$\operatorname{claim} = \forall \operatorname{t} : \mathbb{R} , \exists \operatorname{u} \operatorname{v} : \operatorname{ZMod} 21 , \operatorname{Complex.normSq} (\operatorname{NormedSpace.exp} (\operatorname{SMul.smul} (\operatorname{t}) ((\operatorname{SMul.smul} ((- \operatorname{Complex.I})) (\operatorname{Matrix.reindex} (\operatorname{ZMod.finEquiv} 21) . \operatorname{toEquiv} (\operatorname{ZMod.finEquiv} 21) . \operatorname{toEquiv} ((\operatorname{SimpleGraph.cycleGraph} 21) . \operatorname{adjMatrix} \mathbb{C}))))) \operatorname{u} \operatorname{v}) \neq 1 / 21$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/CycleTwentyOneNoUniformMixing.claim` (`✓ std3`).

*Citation.* A. Ahmadi; R. Belk; C. Tamon; C. Wendler (2003). *On mixing in continuous-time quantum walks on some circulant graphs*. DOI: [10.26421/qic3.6-4](https://doi.org/10.26421/qic3.6-4). URL: <https://arxiv.org/abs/quant-ph/0209106v5>.

*Commentary.*

"No complete cycle $C_{n}$, except for $C_{3}, C_{4}$, has the instantaneous uniform mixing property under the continuous-time quantum walk model." (Ahmadi–Belk–Tamon–Wendler, quant-ph/0209106v5, p. 7, Conjecture 1). The claim here is its C21 case: real time, exp(t • ((−Complex.I) • A)), and an existential pair of vertices. The adjacency is Mathlib cycleGraph(21).adjMatrix, reindexed through ZMod.finEquiv(21).

**Theorem 1.3 (result).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/CycleTwentyOneNoUniformMixing.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alison Gray; Pransu Patel; Isaiah Young (2026). *The cycle C9 does not admit uniform mixing*. URL: <https://arxiv.org/abs/2607.28345v1>.

*Commentary.*

At every real time at least one entry of the transition-probability matrix of C21 differs from 1/21. Fourier correlations give ten cleared polynomial equations; the integer Laurent identity excludes a common nonzero root. This excludes C21 and is partial progress on the Ahmadi–Belk–Tamon–Wendler conjecture.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/CycleTwentyOneNoUniformMixing.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/CycleTwentyOneNoUniformMixing.no_uniform_mixing_of_no_common_nonzero_root`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/CycleTwentyOneNoUniformMixing.result`
- Dependency: [D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIncidenceChecker](OrbitIncidenceChecker.md)
