using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class GaussianStripControlDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Laplace/GaussianStripControl.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Holomorphy and quadratic growth on the strip used for Gaussian Laplace inversion.",
        H("Gaussian strip control"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gaussian-strip-control"),
                DeclarationHandle.Create(Prefix + "GaussianStripControl"),
                H("A wider strip for the regular term"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A complex function J has Gaussian strip control if it is holomorphic "
                    + "where -1/5 < Re(s) < 1 and there is a nonnegative constant C such "
                    + "that its norm is at most C times (1 + abs(Im(s))) squared throughout "
                    + "the closed strip -1/6 <= Re(s) <= 3/4. The constant is independent "
                    + "of both coordinates of s."))),
                DescribeRole.Definition))));
}
