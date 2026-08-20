# Root-Pulse Refinement Depth

## Abstract

The root-pulse chain raises and then lowers completion depth while attaining the finite-state bound.

**Theorem 1.1 (Refinement depth is nonmonotone and the bound is sharp).**

$$\begin{gathered}\forall n \in \mathbb{N}, 3 \leq n \Rightarrow\\m_{*}(r) = 0 \land\\m_{*}(q) = n-2 \land\\m_{*}(e) = 0 \land\\\lvert Z_{r} \rvert = 1 \land\\\lvert Z_{q} \rvert = n \land\\\lvert Z_{e} \rvert = n \land\\((\exists hr: Bool \to PUnit, r = hr \circ q) \land m_{*}(r) = 0 \land m_{*}(r) < m_{*}(q) \land m_{*}(q) = n-2) \land\\((\exists hq: \operatorname{Fin}(n) \to Bool, q = hq \circ e) \land m_{*}(q) = n-2 \land m_{*}(e) = 0 \land m_{*}(e) < m_{*}(q)) \land\\m_{*}(q) = n-2 \land\\n-2 = \lvert \operatorname{Fin}(n) \rvert - \lvert \operatorname{range}(q) \rvert.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/RootPulseRefinementDepth.root_pulse_refinement_depth_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least three, the state carrier is Fin n and the update is truncated predecessor. The three readouts are the constant map r, the root-pulse map q, and the identity map e.

For each readout, the completion state Z is constructed as the quotient by equality of every future readout coordinate. Its depth is the repository observationStabilityDepth, the least index at which two successive finite-word relations agree.

The factorization r = hr composed with q states that q refines r; its depth rises strictly from zero to n minus two. The factorization q = hq composed with e states that e refines q; its depth falls strictly back to zero.

The imported root-pulse sharpness theorem supplies the exact middle depth. Separating future profiles identify the root-pulse and identity completion quotients with Fin n, while the constant completion is a singleton. Surjectivity of q gives a two-element range and hence equality in the finite-state bound.

## References

- Truth anchor: `D5/S3/Observer/Separation/RootPulseRefinementDepth.root_pulse_refinement_depth_counterexample`
- Dependency: [D5/S3/Observer/Separation/RootPulseSharpness](RootPulseSharpness.md)
