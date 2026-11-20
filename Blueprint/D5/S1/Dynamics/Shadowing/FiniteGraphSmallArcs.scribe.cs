using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class FiniteGraphSmallArcsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Images of short immersed arcs in finite graphs",
        H("Images of short immersed arcs in finite graphs"),
        Blocks(Describe.Lean(
            DescribeId.Create("short-immersed-arc-endpoint-diameter"),
            DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/FiniteGraphSmallArcs.injOn_and_diam_image_of_mapsTo_closedBall"),
            H("An immersed interval in a small graph ball is an embedded arc"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A sufficiently small closed ball in the affine realization lies in one edge interval or a small star about a vertex. Any continuous parametrization of a closed interval into the ball that is locally injective in the interior is injective on the interval. Its image diameter is the distance between the two endpoint images."))),
            DescribeRole.Theorem))));
}
