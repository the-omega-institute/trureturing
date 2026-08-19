# Exact Complex Reference-Frame Tax and Optimal Span

## Abstract

The finite exchange model has an exact complex-amplitude tax and an explicitly identified paired sine-mode optimum space.

**Theorem 1.1 (The complex reference-frame tax and optimal span are exact).**

$$\begin{gathered} N \in \mathbb{N},\quad2\leq N\longrightarrow \\ U_{N}^{*} U_{N} = I,\quad n(exchange(x)) = n(x), \\ \forall c \in \mathbb{C}^{N},\quad F_{e}(c) = \lvert Jc\rvert_{2}^{2}, \\ F_{e}^{\mathrm{opt}}(N):=\max_{c \in \mathbb{C}^{N}, \lvert c\rvert_{2}=1} F_{e}(c) = \operatorname{cos}(\frac{\pi}{N+1})^{2}, \\ 1-F_{e}^{\mathrm{opt}}(N) = \sin(\frac{\pi}{N+1})^{2}, \\ 1-F_{e}(m \mapsto 1/\sqrt{N}) = \frac{3}{2N}, \\ \operatorname{eigenspace}(J^{2}, \operatorname{cos}(\frac{\pi}{N+1})^{2}) = \operatorname{span}_{\mathbb{C}}(\{v_{1}, v_{N}\}), \\ \operatorname{finrank}_{\mathbb{C}}(\operatorname{eigenspace}(J^{2}, \operatorname{cos}(\frac{\pi}{N+1})^{2})) = 2 \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrame/ComplexReferenceFrameTaxExactSpan.complex_reference_frame_tax_exact_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For ladders of length at least two, the exchange permutation is unitary and conserves total excitation. For every complex reference vector, the channel entanglement fidelity is exactly the squared norm of zero-boundary nearest-neighbour averaging.

The complex unit sphere has the sharp cosine-squared optimum, so its complementary optimal tax is sine-squared. The normalized flat complex vector has tax three over two N.

The full squared path-average eigenspace at the sharp eigenvalue equals the complex span of the coerced low-edge and high-edge sine modes, and that space has complex dimension two.

The lower bound on N records the frozen one-level counterexample to the flat formula. The proof applies the existing exact complex clauses and reconstructs only the span equality that was previously private.

## References

- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/ComplexReferenceFrameTaxExactSpan.complex_reference_frame_tax_exact_span`
