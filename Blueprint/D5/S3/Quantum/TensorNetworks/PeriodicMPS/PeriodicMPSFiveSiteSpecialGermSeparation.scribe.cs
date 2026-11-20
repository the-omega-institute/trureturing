using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSFiveSiteSpecialGermSeparationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteSpecialGermSeparation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separation of the four normalized special germs",
        H("Separation of the four normalized special germs"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitespecialgermseparation-result"),
            DeclarationHandle.Create(Module + ".specialPoint_germs_distinct"),
            H("Separation of the four normalized special germs"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Local image inclusion between two distinct normalized special lifts would force equality of their certified raw observation germs."))),
            DescribeRole.Theorem))));
}
