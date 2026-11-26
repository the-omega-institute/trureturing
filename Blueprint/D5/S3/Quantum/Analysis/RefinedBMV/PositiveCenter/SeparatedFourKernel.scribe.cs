using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter;

internal sealed class RefinedBMVPositiveCenterSeparatedFourKernelDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mixed derivative on the refined BMV central strip",
        H("Strict mixed derivative negativity from gap four"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-positive-center-central-gap-four"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/SeparatedFourKernel.logKernel_central_gap_four_mixed_lt"),
                H("Strict negativity on the central strip"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural number p at least eleven, the mixed derivative of the original " +
                    "normalized kernel is strictly negative when the lower logarithmic coordinate u is " +
                    "between one half and four and the gap v minus u is at least four. The leading square " +
                    "and the signed linear correction give a positive first derivative in u and a negative " +
                    "mixed derivative before the positive decreasing upper normalization. The radical " +
                    "difference is controlled by averaging its divided difference against a decreasing " +
                    "density. Both mixed derivatives remain strictly negative in the original coordinates."))),
                DescribeRole.Theorem))));
}
