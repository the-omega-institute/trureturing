using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter;

internal sealed class RefinedBMVShortGapTenThirdsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV short-gap sign from ten thirds",
        H("Strict mixed derivative negativity from lower coordinate ten thirds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-short-gap-from-ten-thirds"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ShortGapTenThirds.logKernel_shortGap_mixed_from_ten_thirds"),
                H("Negative mixed derivative at every positive gap through two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural degree p at least eleven and lower logarithmic coordinate " +
                    "u at least ten thirds, the mixed derivative of the normalized kernel is " +
                    "strictly negative for 0 < v − u ≤ 2. The proof combines the existing " +
                    "short-gap profile with a fourth-moment bound and a joint comparison of " +
                    "the radical and normalization derivatives."))),
                DescribeRole.Theorem))));
}
