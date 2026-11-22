using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter;

internal sealed class RefinedBMVPositiveCenterLeftStripKernelDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mixed derivative on the refined BMV left strip",
        H("Strict mixed derivative negativity on the left strip"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-positive-center-left-strip-seven-halves"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripKernel.leftStrip_logKernel_mixed_lt_seven_halves"),
                H("Strict negativity for a gap of at least seven halves"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural number p at least eleven and independent real logarithmic coordinates u and v " +
                    "with zero less than u, u at most one half, and v minus u at least seven halves, the v derivative " +
                    "of the u derivative of the normalized positive-center kernel is strictly negative. " +
                    "The geometric term, the correlated root difference, and the finite exponential tail bound the " +
                    "weighted third derivative of the numerator by strictly less than negative three five-hundredths. " +
                    "A logarithmic derivative bound for the negative marginal and the lower-collision cancellation " +
                    "transfer this margin to the mixed derivative of the normalized kernel."))),
                DescribeRole.Theorem))));
}
