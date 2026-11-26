using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.Tracial;

internal sealed class HingeMomentsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed four-copy arc-count comparison",
        H("Signed four-copy arc-count comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-four-mark-signed-defect"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Analysis/RefinedBMV/Tracial/HingeMoments.integral_fourMarkSignedDefect_lower"),
                H("Coercive comparison of independent and equally spaced marks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For a uniform arc count from four independent marks and the count from a uniformly " +
                    "rotated four-point grid, the exponentially weighted difference of their fourth-product " +
                    "averages controls the square of the signed spectral gap times the sum of the squared " +
                    "spectral values. This is the scalar estimate for the two-insertion term of the " +
                    "four-copy trace comparison near a commuting pair. The proof integrates the three " +
                    "hinge corrections and checks the resulting quadratic form for each power weight."))),
                DescribeRole.Theorem))));
}
