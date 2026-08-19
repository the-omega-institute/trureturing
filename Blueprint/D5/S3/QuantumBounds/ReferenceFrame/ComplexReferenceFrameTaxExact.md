# Exact Complex Reference-Frame Tax

## Abstract

The finite exchange model has an exact complex-amplitude fidelity, tax, and paired top eigenspace.

**Theorem 1.1 (The complex reference-frame tax is exact).**

$$\begin{gathered} N \in \mathbb{N},\quad2\leq N\longrightarrow \\ U_{N}^{*} U_{N} = I,\quad n(exchange(x)) = n(x), \\ \forall c \in \mathbb{C}^{N},\quad F_{e}(c) = \lvert Jc\rvert_{2}^{2}, \\ F_{e}^{\mathrm{opt}}(N):=\max_{c \in \mathbb{C}^{N}, \lvert c\rvert_{2}=1} F_{e}(c) = \operatorname{cos}(\frac{\pi}{N+1})^{2}, \\ 1-F_{e}^{\mathrm{opt}}(N) = \sin(\frac{\pi}{N+1})^{2}, \\ 1-F_{e}(m \mapsto 1/\sqrt{N}) = \frac{3}{2N}, \\ \operatorname{finrank}_{\mathbb{C}}(\operatorname{eigenspace}(J^{2}, \operatorname{cos}(\frac{\pi}{N+1})^{2})) = 2 \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrame/ComplexReferenceFrameTaxExact.complex_reference_frame_tax_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For ladders of length at least two, the exchange permutation is unitary and conserves total excitation. For every complex reference vector, the channel entanglement fidelity is exactly the squared norm of zero-boundary nearest-neighbour averaging.

The complex unit sphere has the same sharp cosine-squared optimum as the real sphere, so the complementary optimal tax is sine-squared. The normalized flat complex vector has tax three over two N.

The squared complex path-average eigenspace at the sharp eigenvalue has complex dimension two. The lower bound on N is necessary because the one-level flat tax is one rather than three halves.

Repository search found exact declarations for all four complex-amplitude clauses in the frozen complexification module; this declaration applies them directly and adds no replacement proof.

## References

- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/ComplexReferenceFrameTaxExact.complex_reference_frame_tax_exact`
- Dependency: [D5/S3/QuantumBounds/ReferenceFrame/Complexification](Complexification.md)
