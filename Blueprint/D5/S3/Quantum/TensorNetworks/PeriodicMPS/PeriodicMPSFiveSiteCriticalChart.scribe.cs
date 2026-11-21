using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSFiveSiteCriticalChartDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteCriticalChart";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Critical minors in the ordinary chart",
        H("Critical minors in the ordinary chart"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitecriticalchart-result"),
            DeclarationHandle.Create(Module + ".relatively_prime_chartMinors"),
            H("Critical minors in the ordinary chart"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The two certified weighted minors remain relatively prime after passing to the affine trace chart."))),
            DescribeRole.Theorem))));
}
