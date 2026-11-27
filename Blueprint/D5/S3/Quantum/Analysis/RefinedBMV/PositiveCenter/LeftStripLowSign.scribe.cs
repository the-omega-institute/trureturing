using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter;

internal sealed class RefinedBMVPositiveCenterLeftStripLowSignDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mixed derivative at the refined BMV left collision",
        H("Strict mixed derivative negativity near the left collision"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-positive-center-left-strip-low"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripLowSign.leftStrip_logKernel_mixed_lt_low"),
                H("Strict negativity for a positive gap of at most one half"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural number p at least eleven and independent real logarithmic coordinates u and v " +
                    "with zero less than u, u at most one half, and v minus u in the interval (0, 1/2], " +
                    "the v derivative of the u derivative of the original log kernel is strictly negative. " +
                    "Factoring the marginal zeros gives a continued expression for the weighted third derivative " +
                    "of the numerator. Taylor remainders and outward-rounded interval bounds give a strict sign " +
                    "at every point needed by the weighted derivative transfer."))),
                DescribeRole.Theorem))));
}
