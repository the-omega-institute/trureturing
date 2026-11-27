using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualModeThreeFloorBudgetTransportDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/ActualModeThreeFloorBudgetTransport";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal Robin budgets exclude short denominators whenever the original integer box misses the window.",
        H("Short denominator exclusion with literal Robin budgets"),
        Blocks(
            Paragraph(Text(
                "For an actual cutoff at X write L = log X. The three signed slopes are L divided by the second cutoff "
                + "offset, and the third and fifth offsets divided by the second. The budget vector keeps the nested "
                + "floor on the first axis and the ordinary floors on the other two. Its reference logarithm may differ from L by at most one.")),
            Describe.Lean(
                DescribeId.Create("floor-budget-errors"),
                DeclarationHandle.Create(Gid + ".floor_budget_errors"),
                H("The literal floors give both label error bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For 37/50 ≤ β < 3/4 and positive budget coefficient, each squared coordinate error is bounded "
                        + "by the full padded sum. The first and second axis budgets grow at least exponentially "
                        + "at rate 1/15 in L. The third layer retains its additional factor L squared. The explicit coefficient "
                        + "is common to both errors, uniformly over all signed integer labels."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-fixed-clock-box-miss-obstruction"),
                DeclarationHandle.Create(Gid + ".exists_fixed_clock_box_miss_obstruction"),
                H("Every late box miss has a large primitive denominator"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The three rounded budgets times the original window width tend uniformly to infinity on the unit "
                        + "reference neighborhood. The exact perturbed integer clock tends to infinity and stays in that neighborhood. "
                        + "The three-axis affine theorem then applies to the original closed integer box and strict window. "
                        + "Its unique primitive label retains the signed phase gap and weighted bound, and its denominator "
                        + "is strictly larger than L divided by 50 log L and at most the reciprocal of the window width."))),
                DescribeRole.Theorem))));
}
