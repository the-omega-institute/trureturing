using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class ActualProtectedZeroPairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact protected pair contribution",
        H("The exact protected pair contribution"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-protected-pair-has-sum"),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualProtectedZeroPair.actual_protected_pair_hasSum"),
            H("The exact protected pair contribution"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Summing every occurrence of the protected actual zero and its conjugate gives a real cosine. Its amplitude uses the analytic multiplicity, coefficient norm and nonzero moment."))),
            DescribeRole.Theorem))));
}
