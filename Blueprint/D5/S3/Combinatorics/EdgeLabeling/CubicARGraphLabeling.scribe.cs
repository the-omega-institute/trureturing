using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.EdgeLabeling;

internal sealed class CubicARGraphLabelingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/EdgeLabeling/CubicARGraphLabeling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bijection from the actual edge set to a finite initial segment supplies positive successor labels on actual edges and zero elsewhere.",
        H("Total edge-label extension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cubicargraphlabeling-edgelabel"),
                DeclarationHandle.Create(Prefix + "edgeLabel"),
                H("Total edge-label extension"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A bijection from the actual edge set to a finite initial segment supplies positive successor labels on actual edges and zero elsewhere."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cubicargraphlabeling-argraph_of_edge_equiv"),
                DeclarationHandle.Create(Prefix + "arGraph_of_edge_equiv"),
                H("From an edge equivalence to additive rigidity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a cubic graph, an edge equivalence with no additive collision at any vertex supplies an exact AR-labeling."))),
                DescribeRole.Theorem))));
}
