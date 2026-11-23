# Singular product-noise decoder perturbation

## Abstract

A quadratic replacement correction realizes a marginal direction at a singular fixed reference.

**Theorem 1.1 (Same-memory marginal displacement).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SingularProductNoiseDecoder.singular_decoder_marginal_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/SingularProductNoiseDecoder.singular_decoder_marginal_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Omega Institute (2026). *Singular product reference recovery through a finite memory*. URL: <https://github.com/the-omega-institute/trureturing/pull/33561>.

*Commentary.*

Let an encoder E and decoder D through finite memory have composite T = D ∘ E fixing a density τ supported on the first block of P ⊕ Q. Its support block is bounded below by m I with m > 0. Let K be Hermitian of trace zero with KQQ ≤ 0. Write ΠQ for the projection onto Q, set Z = ΠQ − (card Q)τ, and take C ≥ 1 + 2‖KPQ‖²/m using the operator norm. There is a cutoff δ in (0, 1] such that for 0 < η ≤ δ the matrix σ = τ − ηK + Cη²Z is a density. The Schur complement uses the support floor m/2, kernel floor Cη² and cross-block norm η‖KPQ‖. Postcompose D with identity and replacement by σ mixed with weights 1 − η and η. The resulting composite Tη has τ − Tη(τ) = η²K − Cη³Z and satisfies the joint residual estimate below.

**Definition 1.2 (Exact joint residual and uniform trace-norm bound).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SingularProductNoiseDecoder.SingularJointErrorExpansion`

*Formalization.* `D5/S3/Quantum/Recovery/LocalCompression/SingularProductNoiseDecoder.SingularJointErrorExpansion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* The Omega Institute (2026). *Singular product reference recovery through a finite memory*. URL: <https://github.com/the-omega-institute/trureturing/pull/33561>.

*Commentary.*

For all reference densities ω and joint densities ρ, write A(S) for the action of S on the second factor and ρR for the reference marginal of ρ. Set X = (1 − η²)ω ⊗ τ + η²ρ, Hη = (X − A(Tη)X)/η² and H = ρ − A(T)ρ + ω ⊗ K. The predicate requires Hη − H to equal η[A(T)ρ − ρR ⊗ σ] − η²ω ⊗ K − (1 − η²)Cη ω ⊗ Z. Its half trace norm is bounded above by η[1 + (‖K‖₁ + C‖Z‖₁)/2]. The channel correction is a multiple of a difference of densities, and tensoring with ω preserves the trace norm.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SingularProductNoiseDecoder.SingularJointErrorExpansion`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SingularProductNoiseDecoder.singular_decoder_marginal_shift`
- Dependency: [D5/S3/Quantum/Recovery/LocalCompression/ProductNoiseDecoder](ProductNoiseDecoder.md)
