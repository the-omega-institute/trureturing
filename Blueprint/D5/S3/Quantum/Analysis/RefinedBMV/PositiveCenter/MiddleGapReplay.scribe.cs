using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter;

internal sealed class RefinedBMVPositiveCenterMiddleGapReplayDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mixed derivative of the refined BMV kernel for lower coordinate at least four",
        H("Strict mixed derivative negativity for lower coordinate at least four"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-positive-center-lower-coordinate-four"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleGapReplay.logKernel_mixed_of_lower_four_le"),
                H("All positive gaps above lower coordinate four"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural degree p at least eleven and logarithmic coordinates 4 ≤ u < v, " +
                    "the v derivative of the u derivative of the original kernel is strictly negative. " +
                    "The proof uses the short-gap sign up to gap two and the analytic tail estimate from gap four. " +
                    "For intermediate gaps, dyadic Taylor enclosures bound the normalized mixed derivative " +
                    "on the boxes of a finite cover."))),
                DescribeRole.Theorem))));
}
