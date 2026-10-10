using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SevenCycleCoherenceResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coherent returns with persistent entry collision", H("Coherent returns with persistent entry collision"),
        Blocks(Describe.Lean(
            DescribeId.Create("sevencyclecoherenceresult-result"),
            DeclarationHandle.Create("D5/S1/Digit/Infinite/SevenCycleCoherenceResult.result"),
            H("Separation is not necessary for return coherence"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The same primitive seven-period rival has a cyclic component "
                + "in the complete original product graph, reached immediately after a distinct-label edge. "
                + "Both source projections and their ordered label pairs have synchronized returns throughout "
                + "the whole component. Nevertheless the fixed entry tail survives every finite future horizon. "
                + "A zero-label head feeds this component and cannot be reached from it. "
                + "The conclusion concerns infinite actual sources and does not assert a failure of finite-source identification."))),
            DescribeRole.Theorem))));
}
