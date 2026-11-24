using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.LocalCompression;

internal sealed class ProductNoiseDecoderDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/omega2026productnoisedecoder");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A physical decoder perturbation realizes any traceless Hermitian marginal direction at a faithful fixed point.",
        H("Faithful product-noise decoder perturbation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("faithful-decoder-marginal-shift"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/LocalCompression/ProductNoiseDecoder."
                    + "faithful_decoder_marginal_shift"),
                H("Exact marginal shift and joint reconstruction error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Let an encoder E and decoder D through a finite memory have composite T = D ∘ E. "
                    + "Suppose T fixes a faithful density τ. For any Hermitian matrix K of trace zero "
                    + "there are L > 0 and a density σ = τ − K/L. For 0 < ε ≤ 1 and εL ≤ 1, "
                    + "postcompose D with the channel that replaces its output by σ with weight εL "
                    + "and applies the identity with weight 1 − εL. Combining the new decoder with "
                    + "E gives Tε and Tε(τ) = τ − εK. The spectral floor of τ bounds the perturbation "
                    + "and trace preservation makes replacement independent of the decoder input. "
                    + "The same Tε satisfies the joint error expansion below for every reference and source."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("product-noise-joint-error-expansion"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/LocalCompression/ProductNoiseDecoder.JointErrorExpansion"),
                H("The scaled joint error and its two corrections"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For arbitrary reference density ω and joint density ρ, set ρR to the reference "
                    + "marginal of ρ and write A(S) for the action of a channel S on the second factor. "
                    + "The noisy state is X = (1 − ε)ω ⊗ τ + ερ. Set H = ρ − A(T)ρ + ω ⊗ K "
                    + "and Hε = (X − A(Tε)X)/ε. The predicate requires Hε − H to equal "
                    + "εL[A(T)ρ − ρR ⊗ τ] + ε[(ρR − ω) ⊗ K] and its half trace norm to be at most "
                    + "ε[L + D(ρR, ω)‖K‖₁], where D denotes half the trace norm of a state difference. "
                    + "The first correction uses the bound of one on trace distance between densities. "
                    + "The second uses trace-norm multiplicativity on tensor products."))),
                DescribeRole.Definition))));
}
