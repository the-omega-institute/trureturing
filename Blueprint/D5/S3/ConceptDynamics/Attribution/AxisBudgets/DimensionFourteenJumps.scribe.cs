using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution.AxisBudgets;

internal sealed class DimensionFourteenJumpsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenJumps.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bound the jump count for a factor at the fourteen-coordinate budget ceiling.",
        H("Rank jumps at budget 640 in dimension fourteen"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ordinary-rank-jumps"),
                DeclarationHandle.Create(Prefix + "rankJumps"),
                H("Ordinary rank jumps"),
                StatementSource.FromAuthor(Disp(new Formula.Relation(
                    Call("RankJumps", F.Id("f")), FormulaRelationOperator.Equal,
                    Call("StrictRankSkippingEdges", F.Id("f"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On a finite vertex set with natural-number ranks, a "
                    + "Boolean edge table, and a distinguished vertex t, retain the true entries "
                    + "from rows other than t whose target rank exceeds the source rank by at least two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fourteen-budget-needs-two-jumps"),
                DeclarationHandle.Create(Prefix + "two_jumps_at_640"),
                H("At least two ordinary jumps in dimension fourteen within budget 640"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix any marked coordinate among fourteen, and a Boolean table "
                        + "between the two copies of the subsets of the other thirteen coordinates. "
                        + "Outside the full-set row, a true entry requires inclusion. At multiplier "
                        + "three each ordinary row and column has odd degree at most three. The full "
                        + "row and column both use the same degree mode: even degree at most two "
                        + "when selected, odd degree at most one otherwise. The cost is four times "
                        + "the sum of one and the number of true entries from ordinary odd rows to odd columns. "
                        + "If the cost is at most 640, there are at least two true entries from "
                        + "ordinary rows whose target rank exceeds the source rank by at least two.")),
                    Paragraph(Text("The deficits at ranks one, three and eleven force at least "
                        + "9, 100 and 50 chargeable diagonals. A budget of 640 leaves 159 chargeable "
                        + "ordinary entries, so those deficits exhaust the charge. The exceptional "
                        + "prefix inflow saturates at two, and the charged diagonals at ranks five, "
                        + "seven and nine vanish. Their layer-cardinality parities are odd, even, "
                        + "odd. The cut parity identity transfers this pattern to ordinary jumps. "
                        + "The four changes after zero padding require at least two jumps."))),
                DescribeRole.Theorem))));
}
