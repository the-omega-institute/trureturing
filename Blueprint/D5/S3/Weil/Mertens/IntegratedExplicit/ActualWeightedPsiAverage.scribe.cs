using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class ActualWeightedPsiAverageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual weighted psi average preserves the leading mode",
        H("The actual weighted psi average preserves the leading mode"),
        Blocks(Describe.Lean(
            DescribeId.Create("exists-corrected-actual-psi-average"),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualWeightedPsiAverage.exists_corrected_actual_psi_average"),
            H("The actual weighted psi average preserves the leading mode"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The exact Chebyshev psi source supplies both tails. A compact probability on the same forward interval gives the weighted mode with errors controlled by the initial remainder and the first Laplace moment."))),
            DescribeRole.Theorem))));
}
