using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class ProjectiveTreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Terminal normalization of a projective tree",
        H("Terminal normalization of a projective tree"),
        Blocks(Describe.Lean(
            DescribeId.Create("sum-terminal-effects"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/ProjectiveTree.sum_terminal_effects"),
            H("Terminal normalization of a projective tree"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The Kraus effects of the fine terminal histories sum to the identity. At an internal node, descendants of a group of outcomes retain the joint pulled-back effect."))),
            DescribeRole.Theorem))));
}
