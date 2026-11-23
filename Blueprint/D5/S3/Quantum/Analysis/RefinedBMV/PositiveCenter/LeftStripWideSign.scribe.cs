using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter;

internal sealed class RefinedBMVPositiveCenterLeftStripWideSignDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mixed derivative of the refined BMV left strip through gap one",
        H("Strict mixed derivative negativity on the left strip through gap one"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-positive-center-left-strip-gap-one"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripWideSign.leftStrip_logKernel_mixed_lt_gap_one"),
                H("Strict negativity for a positive gap of at most one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural number p at least eleven and real logarithmic coordinates u and v " +
                    "with 0 < u ≤ 1/2 and 0 < v − u ≤ 1, the v derivative of the u derivative of the original " +
                    "logarithmic kernel is strictly negative. The interval between zero and u parametrizes " +
                    "the regularized integrand used in the derivative identity. For v at most one, the " +
                    "low-strip bound already makes the integrand positive. From v = 1 to v = 3/2, outward-rounded " +
                    "marginal and joint Taylor enclosures give the same strict sign uniformly in 3/p."))),
                DescribeRole.Theorem))));
}
