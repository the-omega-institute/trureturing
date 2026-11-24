using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter;

internal sealed class RefinedBMVPositiveCenterLeftStripGeometricIntervalSignDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mixed derivative of the refined BMV left strip for gaps from one to three halves",
        H("Strict mixed derivative negativity on the left strip for gaps from one to three halves"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-positive-center-left-strip-gap-one-to-three-halves"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripGeometricIntervalSign.leftStrip_logKernel_mixed_lt_gap_one_to_three_halves"),
                H("Strict negativity for gaps from one to three halves"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural degree p at least eleven and logarithmic coordinates u and v " +
                    "with 0 < u ≤ 1/2 and 1 ≤ v − u ≤ 3/2, the v derivative of the u derivative of the original " +
                    "logarithmic kernel is strictly negative. For each integration coordinate 0 < a < u, " +
                    "the gap v − a lies in [1, 2]. The exact Taylor certificates for the first three bands " +
                    "give scalar positivity throughout that interval, which transfers to the original kernel."))),
                DescribeRole.Theorem))));
}
