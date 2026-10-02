using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.PrimeNumberTheorem;

internal sealed class PntSmoothingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Weil/primenumbertheoremand2026medium");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The smoothed Chebyshev integral has a quantified smoothing error.",
        H("PntSmoothing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("smoothed-chebyshev-integrand"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/PntSmoothing.SmoothedChebyshevIntegrand"),
                H("SmoothedChebyshevIntegrand"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The integrand is minus the logarithmic derivative of zeta times the Mellin transform of the smoothed indicator times the complex power of X."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("smoothed-chebyshev"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/PntSmoothing.SmoothedChebyshev"),
                H("SmoothedChebyshev"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The reading is the normalized vertical integral of that integrand on the line with real part 1 plus the reciprocal of log X."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("smoothed-chebyshev-close"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/PntSmoothing.SmoothedChebyshevClose"),
                H("SmoothedChebyshevClose"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For a nonnegative once continuously differentiable kernel supported in [1/2, 2] with unit multiplicative Haar mass, one positive constant bounds the smoothing error by C times epsilon times X times log X, whenever X is greater than three, epsilon lies strictly between zero and one, and X times epsilon is greater than two."))),
                DescribeRole.Theorem))));
}
