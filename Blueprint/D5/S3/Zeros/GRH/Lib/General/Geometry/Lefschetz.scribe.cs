using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Geometry;

internal sealed class LefschetzDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lefschetz", H("Lefschetz"),
        Blocks(
            Paragraph(Text("Reduced closures of points; free finite group actions are étale; Galois covers generically smooth. Lefschetz local terms of Hecke correspondences rewritten as a sum over marked pairs.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Geometry/Lefschetz.isNullHecke_of_isNullFamily"),
                H("isNullHecke_of_isNullFamily"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let 𝔑 be neat and b in the Hecke algebra, with function f on cosets. If on all deep levels i of the model the combinations ∑ f(q)[m_α ∘ u_{i,q}] satisfy IsNullFamily in weight h for all α, then IsNullHecke holds for b in weight h.")))))));
}
