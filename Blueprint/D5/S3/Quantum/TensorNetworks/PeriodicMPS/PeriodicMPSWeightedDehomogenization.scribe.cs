using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSWeightedDehomogenizationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSWeightedDehomogenization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative primality after weighted dehomogenization",
        H("Relative primality after weighted dehomogenization"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsweighteddehomogenization-result"),
            DeclarationHandle.Create(Module + ".relatively_prime_dehom"),
            H("Relative primality after weighted dehomogenization"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The weighted homogeneous chart construction preserves relative primality under the stated grading assumptions."))),
            DescribeRole.Theorem))));
}
