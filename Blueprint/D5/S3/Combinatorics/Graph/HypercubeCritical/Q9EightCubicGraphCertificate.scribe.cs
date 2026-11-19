using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class Q9EightCubicGraphCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9EightCubicGraphCertificate", H("Triangle-free cubic graphs on eight vertices"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9eightcubicgraphcertificate-structural-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/Q9EightCubicGraphCertificate.cube_or_wagner"),
                H("Triangle-free cubic graphs on eight vertices"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A triangle-free cubic graph on eight vertices is isomorphic to the cube or Wagner graph. The finite check supplies explicit relabelings, and root normalization reduces every graph in the theorem to one of the checked codes."))),
                DescribeRole.Theorem)),
        []));
}
