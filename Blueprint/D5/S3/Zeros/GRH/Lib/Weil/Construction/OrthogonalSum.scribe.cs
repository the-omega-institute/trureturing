using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Construction;

internal sealed class OrthogonalSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonal Sum", H("Orthogonal Sum"),
        Blocks(
            Paragraph(Text("Tensor products of Heisenberg vacuum models; Wiener amalgam bound for coefficients.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Construction/OrthogonalSum.wiener_bound"),
                H("wiener_bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Wiener-type bound: T bounded, κ: W₁ → W a continuous homomorphism, u(0) ≠ 0, ‖Tρ(z+κx)u‖ = ‖g(t(z)+x)‖, g integrable. Some compact B ⊆ W₁ and M give ∑_i ‖Tρ(κφ(i))v‖ ≤ #φ⁻¹(B)·M·‖v‖ for all homomorphisms φ: I → W₁ and all v.")))))));
}
