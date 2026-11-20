using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteCompactSourceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCompactSource";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The compact five-site source",
        H("The compact five-site source"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitecompactsource-result"),
            DeclarationHandle.Create(Module + ".source_isCompact"),
            H("The compact five-site source"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Taking the closure of the ordinary graph inside three projective spaces gives a compact source."))),
            DescribeRole.Theorem))));
}
