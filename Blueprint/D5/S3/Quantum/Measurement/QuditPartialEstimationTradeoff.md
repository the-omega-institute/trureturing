# QuditPartialEstimationTradeoff

## Abstract

Literal occupation operators and the exact qudit partial-estimation frontier.

**Definition 1.1 (claim).**

$$\operatorname{claim} = \left(\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; 1 \le N \Rightarrow \left(2 \le d \Rightarrow \left(\forall G \in \mathbb{R},\; \frac{(N: \mathbb{R})}{(N: \mathbb{R}) + (d: \mathbb{R}) - 1} \le G \Rightarrow \left(G \le \frac{(N: \mathbb{R}) + 1}{(N: \mathbb{R}) + (d: \mathbb{R})} \Rightarrow \operatorname{IsGreatest}\left(\{F: \mathbb{R} | \exists chi \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\{n: \operatorname{Fin}\left(d\right) \to \mathbb{N} // \sum_{i: \operatorname{Fin}\left(d\right)}(n\left(i\right)) = N\}, \operatorname{Fin}\left(d\right)\right), \operatorname{Prod}\left(\{n: \operatorname{Fin}\left(d\right) \to \mathbb{N} // \sum_{i: \operatorname{Fin}\left(d\right)}(n\left(i\right)) = N\}, \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right),\; \operatorname{Matrix}.\operatorname{PosSemidef}\left(chi\right) \land \left(\operatorname{Matrix}.\operatorname{trace}\left(chi\right) = (\operatorname{Nat}.\operatorname{choose}\left(N + d - 1, d - 1\right): \mathbb{C}) \land \left(\operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(chi \cdot \operatorname{RG}\left(N, d\right)\right)\right) = G \land F = \operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(chi \cdot \operatorname{RF}\left(N, d\right)\right)\right)\right)\right)\}, \frac{1}{(N: \mathbb{R}) + (d: \mathbb{R})} + \left(\operatorname{Real}.\operatorname{sqrt}\left(\left((d: \mathbb{R}) - 1\right) \cdot \left(\frac{(N: \mathbb{R}) + 1}{(N: \mathbb{R}) + (d: \mathbb{R})} - G\right)\right) + \operatorname{Real}.\operatorname{sqrt}\left((N: \mathbb{R}) \cdot \left(G - \frac{(N: \mathbb{R})}{(N: \mathbb{R}) + (d: \mathbb{R})}\right)\right)\right)^{2}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/QuditPartialEstimationTradeoff.claim` (`✓ std3`).

*Citation.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

Page 1, Introduction: "Moreover, we also conjecture that the optimal fidelity trade-off for an ensemble of N identical pure states of a d-level system has the form" (2). N and d range over natural numbers with N at least one and d at least two. G ranges over the stated closed real interval. The source equation is encoded in squared form. The set contains exactly the literal PSD-seed output scores with trace D(N,d) and estimation score G; it uses RF and RG from the Section II operators. The arbitrary-instrument covariance reduction is not separately asserted.

**Theorem 1.2 (result).**

$$\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; 1 \le N \Rightarrow \left(2 \le d \Rightarrow \left(\forall G \in \mathbb{R},\; \frac{(N: \mathbb{R})}{(N: \mathbb{R}) + (d: \mathbb{R}) - 1} \le G \Rightarrow \left(G \le \frac{(N: \mathbb{R}) + 1}{(N: \mathbb{R}) + (d: \mathbb{R})} \Rightarrow \operatorname{IsGreatest}\left(\{F: \mathbb{R} | \exists chi \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\{n: \operatorname{Fin}\left(d\right) \to \mathbb{N} // \sum_{i: \operatorname{Fin}\left(d\right)}(n\left(i\right)) = N\}, \operatorname{Fin}\left(d\right)\right), \operatorname{Prod}\left(\{n: \operatorname{Fin}\left(d\right) \to \mathbb{N} // \sum_{i: \operatorname{Fin}\left(d\right)}(n\left(i\right)) = N\}, \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right),\; \operatorname{Matrix}.\operatorname{PosSemidef}\left(chi\right) \land \left(\operatorname{Matrix}.\operatorname{trace}\left(chi\right) = (\operatorname{Nat}.\operatorname{choose}\left(N + d - 1, d - 1\right): \mathbb{C}) \land \left(\operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(chi \cdot \operatorname{RG}\left(N, d\right)\right)\right) = G \land F = \operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(chi \cdot \operatorname{RF}\left(N, d\right)\right)\right)\right)\right)\}, \frac{1}{(N: \mathbb{R}) + (d: \mathbb{R})} + \left(\operatorname{Real}.\operatorname{sqrt}\left(\left((d: \mathbb{R}) - 1\right) \cdot \left(\frac{(N: \mathbb{R}) + 1}{(N: \mathbb{R}) + (d: \mathbb{R})} - G\right)\right) + \operatorname{Real}.\operatorname{sqrt}\left((N: \mathbb{R}) \cdot \left(G - \frac{(N: \mathbb{R})}{(N: \mathbb{R}) + (d: \mathbb{R})}\right)\right)\right)^{2}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/QuditPartialEstimationTradeoff.result` (`✓ std3`). ∎

*Resolves.* `Problems/mista-fiurasek-2006-qudit-partial-estimation` (proved) by `D5/S3/Quantum/Measurement/QuditPartialEstimationTradeoff.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mista-fiurasek-2006-qudit-partial-estimation","declaration_gid":"D5/S3/Quantum/Measurement/QuditPartialEstimationTradeoff.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

Every allowed estimation score has a positive semidefinite seed attaining the curve, and every seed at that score lies below it. Occupation-block dominance proves the upper bound; the normalized reference-block vector gives attainment.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/QuditPartialEstimationTradeoff.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/QuditPartialEstimationTradeoff.result`
- Dependency: [D5/S3/Quantum/BlockNorm/EssentiallyHermitian](../BlockNorm/EssentiallyHermitian.md)
- Dependency: [D5/S3/Quantum/Entanglement/SequentialRegisterCircuit](../Entanglement/SequentialRegisterCircuit.md)
- Dependency: [D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral](OccupationPartialTransposeSpectral.md)
- Dependency: [D5/S3/Quantum/Reduction/IsometricCompression](../Reduction/IsometricCompression.md)
