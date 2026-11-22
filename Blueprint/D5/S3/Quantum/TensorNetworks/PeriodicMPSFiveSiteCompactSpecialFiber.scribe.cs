using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteCompactSpecialFiberDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCompactSpecialFiber";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four-point compact special fiber",
        H("The four-point compact special fiber"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitecompactspecialfiber-result"),
            DeclarationHandle.Create(Module + ".compact_special_fiber_subset"),
            H("The four-point compact special fiber"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Every compact source point over the special observation equals one of the four explicit lifts."))),
            DescribeRole.Theorem))));
}
