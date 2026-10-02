using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.PrimeNumberTheorem;

internal sealed class Smooth1Document : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Weil/primenumbertheoremand2026medium");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mellin convolution gives smooth threshold functions and their analytic bounds.",
        H("Smooth1"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("smooth1"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/Smooth1.Smooth1"),
                H("Smooth1"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The smoothed indicator is the Mellin convolution of the indicator of (0, 1] with the dilation kernel."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("smooth1-properties-below"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/Smooth1.Smooth1Properties_below"),
                H("Smooth1Properties_below"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("A kernel supported in [1/2, 2] with unit multiplicative Haar mass gives a smoothed indicator equal to one for positive x at most 1 minus epsilon times log two, for every positive epsilon."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("smooth1-properties-above"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/Smooth1.Smooth1Properties_above"),
                H("Smooth1Properties_above"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For a kernel supported in [1/2, 2] and epsilon strictly between zero and one, the smoothed indicator vanishes when x is at least 1 plus twice epsilon times log two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mellin-of-smooth1a"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/Smooth1.MellinOfSmooth1a"),
                H("MellinOfSmooth1a"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For a once continuously differentiable kernel supported in [1/2, 2], every positive epsilon and every complex s with positive real part, the Mellin transform of the smoothed indicator equals the Mellin transform of the kernel at epsilon times s divided by s."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("smooth1-continuous-at"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/Smooth1.Smooth1ContinuousAt"),
                H("Smooth1ContinuousAt"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For a nonnegative once continuously differentiable kernel supported in [1/2, 2] and every positive epsilon, its smoothed indicator is continuous at every positive argument."))),
                DescribeRole.Theorem))));
}
