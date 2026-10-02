using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.PrimeNumberTheorem;

internal sealed class PntContourBoundDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Weil/primenumbertheoremand2026medium");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contour deformation controls the smoothed Chebyshev reading.",
        H("PntContourBound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("smoothed-chebyshev-contour-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/PntContourBound.SmoothedChebyshevContourBound"),
                H("SmoothedChebyshevContourBound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For a nonnegative once continuously differentiable kernel supported in [1/2, 2] with unit multiplicative Haar mass and a small-strip holomorphic logarithmic derivative, there is a positive constant for the central vertical piece. Under both explicit punctured-rectangle holomorphy assumptions and the stated strict parameter ordering, the error from the Mellin mass term is at most the sum of the eight remaining contour norms and that central bound."))),
                DescribeRole.Theorem))));
}
