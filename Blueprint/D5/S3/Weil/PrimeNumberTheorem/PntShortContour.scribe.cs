using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.PrimeNumberTheorem;

internal sealed class PntShortContourDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Weil/primenumbertheoremand2026medium");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The short horizontal contour admits a uniform logarithmic-power estimate.",
        H("PntShortContour"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("i4-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/PntShortContour.I4Bound"),
                H("I4Bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For a once continuously differentiable kernel supported in [1/2, 2], a small-strip holomorphic logarithmic derivative, a lower real part strictly between zero and one, and A strictly positive and at most one half, there are a nonnegative bound constant and a T threshold greater than three. Above that threshold the short horizontal piece satisfies the stated logarithmic-power bound for X greater than three and epsilon strictly between zero and one."))),
                DescribeRole.Theorem))));
}
