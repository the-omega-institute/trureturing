using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSFiveSiteCriticalRankDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteCriticalRank";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rank defect of the normalized five-site observation",
        H("Rank defect of the normalized five-site observation"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitecriticalrank-result"),
            DeclarationHandle.Create(Module + ".evaluated_minor_eq_zero_of_kernel"),
            H("Rank defect of the normalized five-site observation"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "A nonzero real kernel direction forces the evaluated complexified minors to vanish."))),
            DescribeRole.Theorem))));
}
