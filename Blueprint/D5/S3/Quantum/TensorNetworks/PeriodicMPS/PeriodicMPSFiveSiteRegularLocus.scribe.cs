using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSFiveSiteRegularLocusDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteRegularLocus";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The regular five-site locus",
        H("The regular five-site locus"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesiteregularlocus-result"),
            DeclarationHandle.Create(Module + ".isPathConnected_good"),
            H("The regular five-site locus"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Removing the observations of boundary and critical points leaves a path-connected subset of the compact source."))),
            DescribeRole.Theorem))));
}
