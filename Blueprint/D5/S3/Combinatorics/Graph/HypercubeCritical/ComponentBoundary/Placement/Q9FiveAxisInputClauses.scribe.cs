using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisInputClausesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The input clauses express the local cubic, signed, and contact laws in the signed occupancy valuation. The replay matches each reconstructed proposition to its actual clause.",
        H("Input clauses from geometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("translated-clause"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisInputClauses.translated_clause"),
                H("Input clauses from geometry"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The input clauses express the local cubic, signed, and contact laws in the signed occupancy valuation. The replay matches each reconstructed proposition to its actual clause."))),
                DescribeRole.Theorem)),
        []));
}
