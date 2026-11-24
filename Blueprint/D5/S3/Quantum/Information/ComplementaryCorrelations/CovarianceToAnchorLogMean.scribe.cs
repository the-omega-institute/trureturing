using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ComplementaryCorrelations;

internal sealed class CovarianceToAnchorLogMeanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Simpson bound for the logarithmic mean.",
        H("A Simpson bound for the logarithmic mean"),
        Blocks(
            Describe.Lean(DescribeId.Create("qian-covariancetoanchorlogmean-logarithmic-mean-le-simpson"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/CovarianceToAnchorLogMean.logarithmic_mean_le_simpson"),
                H("The positive scalar bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The logarithmic mean of two positive numbers is at most one sixth of their sum plus two thirds of their geometric mean. The unequal case uses the hyperbolic sine and cosine inequality, and the equal case is an equality."))), DescribeRole.Theorem))));
}
