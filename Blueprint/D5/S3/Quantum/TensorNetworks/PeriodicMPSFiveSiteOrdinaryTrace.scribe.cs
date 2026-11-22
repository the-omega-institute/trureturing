using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteOrdinaryTraceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteOrdinaryTrace";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordinary trace chart",
        H("The ordinary trace chart"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesiteordinarytrace-result"),
            DeclarationHandle.Create(Module + ".dense_chartDomain"),
            H("The ordinary trace chart"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The ordinary chart is dense in the compact source of five-site amplitudes and their trace and pencil directions."))),
            DescribeRole.Theorem))));
}
