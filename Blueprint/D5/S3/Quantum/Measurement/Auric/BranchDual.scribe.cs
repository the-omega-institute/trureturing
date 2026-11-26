using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class BranchDualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted score bound for two flagged operations",
        H("Weighted score bound for two flagged operations"),
        Blocks(Describe.Lean(
            DescribeId.Create("two-flag-cp-branch-score-le"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/BranchDual.two_flag_cp_branch_score_le"),
            H("Weighted score bound for two flagged operations"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A common positive dual weight bounds the sum of the two Choi pairings of a normalized branch. The infimum of trace-square-root bounds follows by regularization."))),
            DescribeRole.Theorem))));
}
