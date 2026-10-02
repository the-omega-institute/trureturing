using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.PrimeNumberTheorem;

internal sealed class MellinCalculusDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Weil/primenumbertheoremand2026medium");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compactly supported Mellin kernels have uniform vertical-strip decay.",
        H("MellinCalculus"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mellin-convolution"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/MellinCalculus.MellinConvolution"),
                H("MellinConvolution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Multiplicative convolution integrates f(y) times g(x/y) against dy/y over the positive real axis."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mellin-of-psi"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/MellinCalculus.MellinOfPsi"),
                H("MellinOfPsi"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every once continuously differentiable real kernel supported in [1/2, 2], one positive constant bounds its complex Mellin transform by that constant divided by the norm of the transform parameter. The bound applies uniformly when the real part is positive and at most two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("delta-spike"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/MellinCalculus.DeltaSpike"),
                H("DeltaSpike"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The dilation kernel composes the input kernel with x raised to the reciprocal of epsilon, then divides its value by epsilon."))),
                DescribeRole.Definition))));
}
