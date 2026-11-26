using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LeaflessDynamics;

internal sealed class TripleEdgeSubdivisionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/LeaflessDynamics/TripleEdgeSubdivision.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three-segment subdivision of finite multigraphs",
        H("Three-segment subdivision of finite multigraphs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("triple-edge-subdivision-connectivity"),
                DeclarationHandle.Create(Owner + "connected"),
                H("Subdivision preserves connectivity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Replace each edge by the path through its two incidence flags. Paths between original vertices lift by traversing these paths, and each new flag vertex has a path to an original vertex."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("triple-edge-subdivision-leafless"),
                DeclarationHandle.Create(Owner + "leafless_iff"),
                H("Subdivision preserves the degree-one condition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original vertices retain the number of incident flags and each new flag vertex has degree two. The two flags of a loop both contribute."))),
                DescribeRole.Theorem))));
}
