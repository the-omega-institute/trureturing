using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SevenCycleCollisionResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A persistent seven-cycle entry collision", H("A persistent seven-cycle entry collision"),
        Blocks(Describe.Lean(
            DescribeId.Create("sevencyclecollisionresult-result"),
            DeclarationHandle.Create("D5/S1/Digit/Infinite/SevenCycleCollisionResult.result"),
            H("Failure of universal finite-future separation"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "A positive observation budget strictly below the critical radius admits an "
                + "actual rival with primitive window period seven. Its original singleton orbit "
                + "belongs to the complete endpoint graph. Two different first labels admit "
                + "first colors one and two against that same rival, and one fixed literal first "
                + "tail survives every finite future horizon. The actual entry records have "
                + "fixed common future errors and a uniform positive margin. The sources "
                + "are not eventually null. This refutes the universal "
                + "unconditional finite-future separation assertion."))), DescribeRole.Theorem))));
}
