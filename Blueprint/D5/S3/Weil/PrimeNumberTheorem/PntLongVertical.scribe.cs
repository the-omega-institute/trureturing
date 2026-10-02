using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.PrimeNumberTheorem;

internal sealed class PntLongVerticalDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Weil/primenumbertheoremand2026medium");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The long vertical contour admits a uniform logarithmic-power estimate.",
        H("PntLongVertical"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("i3-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/PntLongVertical.I3Bound"),
                H("I3Bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Let the real smoothing kernel be continuously differentiable and supported in [1/2, 2]. Assume LogDerivZetaHasBound A Cζ, with Cζ positive and 0 < A ≤ 1/2. There is a positive constant C such that, for every X > 3, T > 3 and 0 < epsilon < 1, setting sigma₁ = 1 − A/(log T)^9 gives the bound ‖I₃‖ ≤ C times X times X to the power −A/(log T)^9, divided by epsilon."))),
                DescribeRole.Theorem))));
}
