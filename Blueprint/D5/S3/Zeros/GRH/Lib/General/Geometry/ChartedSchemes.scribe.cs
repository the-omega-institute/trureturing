using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Geometry;

internal sealed class ChartedSchemesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Charted Schemes", H("Charted Schemes"),
        Blocks(
            Paragraph(Text("Bijectivity of a comparison defines a closed class; charted schemes (IsCharted).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Geometry/ChartedSchemes.isClosedClass"),
                H("isClosedClass"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Given a comparison c from F to F' along φ, functors ψ, ψ' to D and η: ψ' → ψ∘φ, the property of N on D that c along N(η) is bijective in every degree holds for 0 and passes along short exact sequences (IsClosedClass).")))))));
}
