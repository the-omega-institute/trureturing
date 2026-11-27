using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisSignedRowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Products of the switching signs along occupied edges determine which endpoint sign variables agree. Zero-sum exterior rows yield an opposite signed occupied neighbor.",
        H("Signed edge and polarity conditions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("edge-sign-iff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisSignedRows.edge_sign_iff"),
                H("Signed edge and polarity conditions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Products of the switching signs along occupied edges determine which endpoint sign variables agree. Zero-sum exterior rows yield an opposite signed occupied neighbor."))),
                DescribeRole.Theorem)),
        []));
}
