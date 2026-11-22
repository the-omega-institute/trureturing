using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteNormalizationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteNormalization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalization of the special five-site observation",
        H("Normalization of the special five-site observation"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitenormalization-result"),
            DeclarationHandle.Create(Module + ".normalized_special_fiber"),
            H("Normalization of the special five-site observation"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Equality of the normalized special observations constrains the amplitude to one of the explicit rays."))),
            DescribeRole.Theorem))));
}
