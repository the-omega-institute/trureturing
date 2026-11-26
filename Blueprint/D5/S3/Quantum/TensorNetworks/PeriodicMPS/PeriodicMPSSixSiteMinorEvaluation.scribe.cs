using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteMinorEvaluationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact triangular certificates for six-site point values",
        H("Exact triangular certificates for six-site point values"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsiteminorevaluation-value-of-factors"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorEvaluation.value_of_factors"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A unit lower triangular factor and an upper triangular factor give the signed determinant value by the diagonal product."))), DescribeRole.Theorem))));
}
