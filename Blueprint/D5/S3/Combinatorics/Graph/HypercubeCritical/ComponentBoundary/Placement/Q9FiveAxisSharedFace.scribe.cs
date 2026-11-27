using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisSharedFaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both exterior midpoints see exactly the same two occupied corners. The two face swaps change the relative sign, which prevents cancellation at both midpoints.",
        H("A shared face excludes the second orbit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-second-orbit"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisSharedFace.no_second_orbit"),
                H("A shared face excludes the second orbit"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both exterior midpoints see exactly the same two occupied corners. The two face swaps change the relative sign, which prevents cancellation at both midpoints."))),
                DescribeRole.Theorem)),
        []));
}
