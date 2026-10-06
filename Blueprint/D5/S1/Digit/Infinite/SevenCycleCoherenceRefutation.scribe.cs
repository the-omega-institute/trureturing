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
            Blocks(Paragraph(Text("The assertion requires finite future separation whenever an actual "
                + "odd primitive singleton rival belongs to a cyclic component reachable after a first "
                + "source-label divergence. Coherence is the least-common-multiple synchronization "
                + "of every pair of nonempty returns, for each projection and for ordered source pairs. "
                + "The product graph retains all original pieces, permitted colors and full containment edges."))),
            DescribeRole.Definition))));
}
