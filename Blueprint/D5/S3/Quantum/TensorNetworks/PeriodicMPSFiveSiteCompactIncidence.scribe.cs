using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteCompactIncidenceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCompactIncidence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Incidence identities on the compact five-site source",
        H("Incidence identities on the compact five-site source"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitecompactincidence-result"),
            DeclarationHandle.Create(Module + ".compact_incidence"),
            H("Incidence identities on the compact five-site source"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Polynomial identities relating the trace, pencil and amplitude directions extend from the ordinary graph to its closure."))),
            DescribeRole.Theorem))));
}
