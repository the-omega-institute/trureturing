using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSFiveSiteSpecialRegularDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteSpecialRegular";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regularity of the special lifts",
        H("Regularity of the special lifts"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitespecialregular-result"),
            DeclarationHandle.Create(Module + ".specialPoint_regular"),
            H("Regularity of the special lifts"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The normalized observation has injective differential at each of the four special lifts."))),
            DescribeRole.Theorem))));
}
