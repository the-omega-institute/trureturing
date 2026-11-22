using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSFiveSiteSpecialGermsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteSpecialGerms";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized special lifts",
        H("The normalized special lifts"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitespecialgerms-result"),
            DeclarationHandle.Create(Module + ".specialPoint_exhausts"),
            H("The normalized special lifts"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The four raw observation centers map to the entire compact fiber over the special observation."))),
            DescribeRole.Theorem))));
}
