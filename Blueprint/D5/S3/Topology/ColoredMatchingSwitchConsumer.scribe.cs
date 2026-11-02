using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class ColoredMatchingSwitchConsumerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Circle changes at an actual weaving crossing.", H("Circle changes at an actual weaving crossing"), Blocks(
            Paragraph(Text("Let P have n at least two and m at least three, let p be either parity, and let S be any finite crossing subset. Insert a crossing z outside S. The four actual ports at z are pairwise distinct, and the new mixed matching agrees with the old one away from these ports.")),
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Topology/ColoredMatchingSwitchConsumer.mixed_insert_circle_count"),
                H("Circle changes at an actual weaving crossing"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The generic colored matching surgery gives an absolute integer circle-count change at most one. If the two reference endpoint components at z are distinct in the spanning graph on S, the descended mixed-component map puts the two old local arcs in distinct mixed circles; the insertion therefore reduces the circle count by exactly one. No rank formula or global arbitrary-state circle identity is assumed. The result applies to empty, disconnected and almost-full states, and includes the cyclic closing seam."))), DescribeRole.Theorem),
            Paragraph(Text("These finite matching statements are auxiliary to weaving coefficient asymptotics. They do not identify a state polynomial with the source trace-defined Jones invariant or establish the original twist-number limit.")))));
}
