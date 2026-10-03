using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Mordell;

internal sealed class CanonicalPointHeightDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/tauceti2026canonicalheight");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Convergence and the exact quadratic height law.",
        H("Convergence and the exact quadratic height law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-height-properties"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/CanonicalPointHeight.canonicalHeight_properties"),
                H("Convergence and the exact quadratic height law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For a field with admissible absolute values and an elliptic Weierstrass curve, the sequence h(2^n P)/(2 times 4^n) converges to canonicalHeight(P) for every point P. One real constant D bounds the absolute difference between canonicalHeight(P) and h(P)/2 for every P. For all P and Q, the heights of P + Q and P - Q sum to twice the sum of their heights. These conclusions require no Northcott assumption.")),
                    Paragraph(Text("The symmetric-square identity and projective height estimates give a uniform two-point defect. Its specialization to doubling gives summable successive differences, convergence and the bounded comparison. Dividing the full defect by 2 times 4^n and passing to the limit gives the exact parallelogram law. The normalization is half the projective x-coordinate height; positive height from infinite order additionally uses Northcott."))),
                DescribeRole.Theorem))));
}
