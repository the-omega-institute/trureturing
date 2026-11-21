using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class FiniteGraphBowenArcsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Forward separation of immersed short arcs",
        H("Forward separation of immersed short arcs"),
        Blocks(Describe.Lean(
            DescribeId.Create("immersed-short-path-forward-separation"),
            DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/FiniteGraphBowenArcs.separates_points_of_immersed_paths"),
            H("Short paths immersed by every iterate have a uniform separation scale"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("As long as the endpoints of a short immersed arc stay close, continuity keeps the next image in an edge interval or small vertex star. There the image diameter is the distance between its endpoints. With no separating time the entire nondegenerate arc would remain in a single forward Bowen ball, contradicting its finite cardinal bound."))),
            DescribeRole.Theorem))));
}
