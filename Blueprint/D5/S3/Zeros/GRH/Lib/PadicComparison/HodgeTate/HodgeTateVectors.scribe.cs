using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.HodgeTate;

internal sealed class HodgeTateVectorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hodge Tate Vectors", H("Hodge Tate Vectors"),
        Blocks(
            Paragraph(Text("Hodge classes map naturally to vectors of Hodge–Tate weight h in étale cohomology.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/HodgeTateVectors.exists_hasHodgeTateWeight"),
                H("exists_hasHodgeTateWeight"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let Y (smooth, charted over Ω) and W be proper over R, A a place of Ω above p containing R, k ≅ Q̄_p compatibly over E. For x ∈ Hdg^q(Y_E), some v ∈ ℂ_p ⊗ V^{q+h}(Y) of Hodge–Tate weight h for the decomposition group of A over E and semilinear Θ satisfy λ_h(u^*x) = Θ(u^*v) for all u: W → Y.")))))));
}
