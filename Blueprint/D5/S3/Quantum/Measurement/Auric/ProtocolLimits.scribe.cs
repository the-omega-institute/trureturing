using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class ProtocolLimitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace mass controls the stopping approximation",
        H("Trace mass controls the stopping approximation"),
        Blocks(Describe.Lean(
            DescribeId.Create("almost-sure-truncations"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/ProtocolLimits.inClosure_of_almost_sure_truncations"),
            H("Trace mass controls the stopping approximation"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("An input-independent measurable law of finite trees has a finite representation by its Choi moments. Two completely positive continuation maps give a uniform amplified error bound in terms of the unfinished mass."))),
            DescribeRole.Theorem))));
}
