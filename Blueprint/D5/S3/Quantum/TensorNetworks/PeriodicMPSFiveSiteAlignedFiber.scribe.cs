using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteAlignedFiberDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteAlignedFiber";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary lifts of the five-site special ray",
        H("Ordinary lifts of the five-site special ray"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitealignedfiber-result"),
            DeclarationHandle.Create(Module + ".ordinary_lifts"),
            H("Ordinary lifts of the five-site special ray"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The aligned coordinates restrict ordinary lifts of the special ray to two explicit alternatives for each sign."))),
            DescribeRole.Theorem))));
}
