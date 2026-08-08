# CHSH Spectrum and Cubic Coefficient

## Abstract

A conditional CHSH spectral bound supports an exact cubic coefficient.

**Theorem 1.1 (The paired gap coefficient has a closed form).**

$$0<N<4,\quad a^{2}=4+N,\quad b^{2}=4-N\Rightarrow K(N):=\frac{2}{16N^{2}a^{2}}+\frac{2}{16N^{2}b^{2}}=\frac{1}{N^{2}(16-N^{2})}.$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CHSHSpectrum.chsh_cubic_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N, a, and b be real, with 0 < N < 4, a squared equal to 4 + N, and b squared equal to 4 - N. The formal statement starts from the paired four-vertex gap expression: the two vertices of magnitude a contribute the first summand, and the two vertices of magnitude b contribute the second. Clearing its nonzero denominators and using a squared times b squared equal to 16 - N squared gives the displayed rational function exactly.

This is the real-algebra coefficient identity. It introduces no random state or observable measure and makes no asymptotic assertion.

**Theorem 1.2 (Landau's square law constrains the CHSH spectrum).**

$$\begin{gathered} 0<N<4,\quad S^{2}=4I+C,\\ \operatorname{spectrum}_{\mathbb{R}}(C)\subseteq \{N,-N\}\Rightarrow \\ \operatorname{spectrum}_{\mathbb{R}}(S)\subseteq \{\sqrt{4+N},-\sqrt{4+N},\sqrt{4-N},-\sqrt{4-N}\}. \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CHSHSpectrum.chsh_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formal theorem proves the algebraic kernel under an explicit spectral hypothesis. It takes four finite complex Hermitian involutions, forms their CHSH matrix S and the negative Kronecker product C of the two local commutators, and assumes the two-point bound `hC`, namely that the real spectrum of C is contained in {N, -N}. It reuses `landau_identity` for S squared equal to 4I + C and proves S Hermitian from the four input observables. Power spectral mapping sends each real eigenvalue of S to the spectrum of S squared; scalar-shift transport and `hC` then yield the displayed four-point spectral inclusion for S.

Accordingly, the conclusion is an inclusion rather than an equality: it does not assert that all four values occur or establish their multiplicities. Deriving `hC` from the norm identity N equal to the norm of the tensor product of the two local commutators is an independent tensor-commutator obligation and remains open beyond this module. The epsilon-cubed probability law and its Dirichlet-volume argument are likewise outside this module's scope; no probability formula, volume coefficient, or limiting error term is asserted here.

## References

- Truth anchor: `D5/S3/QuantumBounds/CHSHSpectrum.chsh_cubic_coefficient`
- Truth anchor: `D5/S3/QuantumBounds/CHSHSpectrum.chsh_spectrum`
- Dependency: [D5/S3/QuantumBounds/LandauIdentity](LandauIdentity.md)
