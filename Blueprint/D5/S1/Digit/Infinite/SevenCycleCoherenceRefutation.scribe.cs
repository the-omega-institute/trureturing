using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SevenCycleCoherenceRefutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separation as a claimed necessity for coherence.",
        H("Separation as a claimed necessity for coherence"),
        Blocks(Describe.Lean(
            DescribeId.Create("sevencyclecoherencerefutation-claim"),
            DeclarationHandle.Create("D5/S1/Digit/Infinite/SevenCycleCoherenceRefutation.claim"),
            H("Necessary finite separation assertion"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The assertion quantifies over every positive subcritical budget and "
                + "original endpoint graph. It requires finite future separation whenever an actual odd "
                + "primitive singleton rival has its first shifted singleton, with its actual guard, as the "
                + "second projection of a vertex in a "
                + "cyclic strongly connected component reachable from the two zero initial guards after an "
                + "equal-label history and its first unequal-label edge, and "
                + "that component's returns satisfy the original synchronization condition for both source "
                + "projections and for ordered source pairs. For each of these three labelings, coherence "
                + "means that at some component vertex every pair of nonempty returns synchronizes at the "
                + "least common multiple of their lengths. "
                + "The product graph retains all original pieces, permitted colors and full containment edges."))),
            DescribeRole.Definition))));
}
