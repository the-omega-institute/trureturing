using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class CoherentSlackDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive majorant on each coherent flag block",
        H("Positive majorant on each coherent flag block"),
        Blocks(Describe.Lean(
            DescribeId.Create("coherent-flag-majorized"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/CoherentSlack.coherent_flag_majorized"),
            H("Positive majorant on each coherent flag block"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The matching scalar conditions give a diagonal-plus-symmetric block decomposition of the difference. Its two-dimensional determinant and diagonal inequalities establish positivity."))),
            DescribeRole.Theorem))));
}
