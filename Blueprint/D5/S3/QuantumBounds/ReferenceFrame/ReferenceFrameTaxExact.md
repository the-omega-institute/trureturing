# Exact Finite Reference-Frame Tax

## Abstract

The finite exchange model has an exact fidelity bridge, sharp tax, restricted flat tax, and paired top eigenspace.

**Theorem 1.1 (The finite reference-frame tax is exact).**

$$\begin{gathered} N \in \mathbb{N},\quad2\leq N\longrightarrow \\ U_{N}^{*} U_{N} = I,\quad n(exchange(x)) = n(x), \\ \mathcal{E}_{c}(\rho) = \sum_{r \in \operatorname{Fin}(N)} K_{r} \rho K_{r}^{*}, \\ F_{e}(c) = Q_{N}(c) = \lvert Jc\rvert_{2}^{2}, \\ F_{e}^{\mathrm{opt}}(N):=\max_{\sum_{i} c_{i}^{2}=1} F_{e}(c) = \operatorname{cos}(\frac{\pi}{N+1})^{2}, \\ 1-F_{e}^{\mathrm{opt}}(N) = \sin(\frac{\pi}{N+1})^{2}, \\ 2\leq N \longrightarrow 1-Q_{N}((\frac{1}{\sqrt{N}})_{m \in \operatorname{Fin}(N)}) = \frac{3}{2N}, \\ \operatorname{squaredTopEigenspace}(N) = \operatorname{topModeSpace}(N),\quad\operatorname{finrank}_{\mathbb{R}}(\operatorname{squaredTopEigenspace}(N)) = 2 \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrame/ReferenceFrameTaxExact.reference_frame_tax_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The declaration packages the concrete exchange permutation, its conservation law, the finite Kraus representation, and both exact fidelity forms. It then applies the frozen sharp quadratic bound, the sine identity, the flat identity for ladders of length at least two, and the imported paired top-eigenspace characterization.

The lower bound on the ladder length is explicit because the one-level flat calculation has tax one rather than the displayed three-halves formula.

## References

- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/ReferenceFrameTaxExact.reference_frame_tax_exact`
- Dependency: [D5/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge](ChannelFidelityBridge.md)
- Dependency: [D5/S3/QuantumBounds/ReferenceFrame/TopEigenspace](TopEigenspace.md)
