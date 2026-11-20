using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteCriticalRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six-site rank deficit forces the critical equations",
        H("The six-site rank deficit forces the critical equations"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsitecriticalrank-evaluated-minor-eq-zero-of-kernel"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCriticalRank.evaluated_minor_eq_zero_of_kernel"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A nonzero real kernel direction and the independent Euler direction give two complex Jacobian kernel directions, so the selected cofactors vanish."))), DescribeRole.Theorem))));
}
