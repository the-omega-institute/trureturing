using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.Extension;

internal sealed class ArcExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arc Extension", H("Arc Extension"),
        Blocks(
            Paragraph(Text("Polarisation-multiplying isogenies of complex tori extend to abelian schemes over valuation rings.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/Extension/ArcExtension.exists_hom_of_hasThetaCoords"),
                H("exists_hom_of_hasThetaCoords"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let A = V/Λ over O and s': V → A'(O) additive killing Λ, with embeddings N, M obeying the parallelogram law and theta coordinates of positive type (B, χ), resp. (μB, χ^μ). If Λ^∨ maps into K(N) and nΛ^∨ ⊂ Λ, n a unit, then s' comes from a homomorphism ψ with ψ^*[M] = μ[N].")))))));
}
