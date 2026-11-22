using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualRoundingGapEstimatesDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/ActualRoundingGapEstimates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Global bounds and an exact two-candidate formula for the integer rounding gap.",
        H("Finite integer rounding estimates"),
        Blocks(
            Paragraph(Text(
                "Let p be a real base greater than one, λ a positive real price, and C = 1 + 1/λ. "
                + "Write G for BoundaryPrimePrice.integerGap p λ, the smaller loss at the floor and ceiling "
                + "of the real boundary exponent. Write u = 1/p², v = 1/p³ and w = 1/C.")),
            Describe.Lean(
                DescribeId.Create("actual-rounding-global-bounds"),
                DeclarationHandle.Create(Gid + ".integer_gap_global_bounds"),
                H("Two global upper bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every such p and λ, the three simultaneous inequalities are "
                        + "0 ≤ G, G ≤ λ log p and G ≤ −log(1 − u). Rounding upward costs at most "
                        + "one unit of price because the benefit is increasing. Rounding downward "
                        + "loses at most the remaining benefit beyond exponent one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-rounding-chamber-identity"),
                DeclarationHandle.Create(Gid + ".integer_gap_chamber_identity"),
                H("Exact formula between the second and third powers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "When p² < C < p³, the real exponent is strictly between one and two, "
                        + "so the adjacent integers are exactly one and two. The gap equals "
                        + "min(−log(1 − u), −log(1 − v) + λ log p) "
                        + "minus (−log(1 − w) + λ log(C/p²)). "
                        + "The minimum retains both candidates, including ties."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-rounding-chamber-error"),
                DeclarationHandle.Create(Gid + ".integer_gap_chamber_error"),
                H("Error of the simpler chamber profile"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same strict chamber inequalities, the absolute difference "
                        + "between G and min(u, λ log p) is at most "
                        + "w/(1 − w) + λ log(C/p²) + u²/(1 − u) + v/(1 − v). "
                        + "The logarithmic deficit bounds control the change in each "
                        + "candidate and the common subtraction in the exact identity."))),
                DescribeRole.Theorem))));
}
