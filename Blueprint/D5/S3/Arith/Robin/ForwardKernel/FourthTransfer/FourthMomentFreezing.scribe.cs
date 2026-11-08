using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.FourthTransfer;

internal sealed class FourthMomentFreezingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentFreezing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local fourth energy controls normalized moving and frozen increments.",
        H("Fourth-order macroscopic freezing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("macro-fourth-comparison"),
                DeclarationHandle.Create(Prefix + "macro_fourth_comparison"),
                H("Comparison with a fixed length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a bounded continuously differentiable macroscopic length, compare the moving increment with a fixed increment on any subinterval of [X,2X]. If their endpoint gap is at most R and the endpoint scale is admissible, the fourth energy is bounded by (1312/3)C R squared log(X) squared times the image interval length plus the local error. The common endpoint geometry supplies derivatives at least one half and the common image interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("freezing-fourth-finite"),
                DeclarationHandle.Create(Prefix + "freezing_fourth_finite"),
                H("Finite fourth-order freezing estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For n positive equal cells and R=(1+L)X to the theta divided by n, the fourth moment of the normalized moving-minus-frozen increment is at most 1312 C (1+L) squared divided by (3 n squared log 2), multiplied by 1+n M X to the theta divided by X+n epsilon. Frozen functions use disjoint left-open right-closed cells. The local comparison keeps the cell length, so summing produces decay of order n to the minus two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moving-fourth-uniform"),
                DeclarationHandle.Create(Prefix + "moving_fourth_uniform"),
                H("Uniform moving fourth moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under local fourth energy, for every M at least one and nonnegative derivative bound L, all sufficiently large X satisfy the same fourth-moment bound 1312 C M squared divided by log 2 for every admissible length function. The threshold precedes the function quantifier. Taking endpoint radius M X to the theta also covers lengths arbitrarily close to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("frozen-fourth-uniform"),
                DeclarationHandle.Create(Prefix + "frozen_fourth_uniform"),
                H("Uniform frozen fourth moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each fixed positive number of cells, all sufficiently large X give fourth moment at most 1312 C M squared divided by log 2 for every frozen admissible length. On each cell the common endpoint estimate uses radius M X to the theta, and the summed finite bound contains 1+n M X to the theta divided by X+n epsilon. Both error terms eventually lie below one. This controls the whole frozen function for use in Holder estimates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("freezing-fourth-eventually"),
                DeclarationHandle.Create(Prefix + "freezing_fourth_eventually"),
                H("Uniform eventual fourth-order freezing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive tolerance and fixed positive cell count, there is a common eventual threshold for all admissible length functions. Beyond it, the fourth moment of the normalized freezing error is at most 1312 C (1+L) squared divided by (3 n squared log 2) plus the tolerance. The proof uses the explicit finite bound and the vanishing relative endpoint scale and local energy error; it includes the case C equals zero."))),
                DescribeRole.Theorem))));
}
