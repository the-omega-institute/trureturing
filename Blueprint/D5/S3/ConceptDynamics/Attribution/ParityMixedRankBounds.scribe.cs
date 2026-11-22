using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParityMixedRankBoundsDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        var n = F.Id("n");
        var rows = F.Id("R");
        var columns = F.Id("C");
        var table = F.Id("m");
        return Disp(new Formula.Logic(
            Call("OddMargins", n, table),
            FormulaLogicOperator.Implies,
            Seq(Call("MixedRankDeficits", n, table, rows, columns), Sp, Le, Sp,
                Call("EligibleIntervalScore", n, table, rows, columns))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Combine exact row and column rank deficits in a parity table with odd margins.",
        H("Combine row and column cuts on one parity table"),
        Blocks(Describe.Lean(
            DescribeId.Create("mixed-odd-parity-rank-deficits"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Attribution/ParityMixedRankBounds.mixed_rank_lower"),
            H("Mixed rank deficits under odd margins"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Rows are all even subsets of the coordinates and columns are "
                    + "all odd subsets. The table has a row containing every coordinate. Row and "
                    + "column sums are odd and can vary. Every subtraction is natural subtraction.")),
                Paragraph(Text("The row deficit at a selected threshold is the number of ordinary "
                    + "even rows of at least that weight minus their mass in odd columns of weight "
                    + "at most the complementary rank. The column deficit is the number of odd "
                    + "columns above the complementary rank minus the mass they receive from the "
                    + "full row and all lower-weight rows. A threshold selected on both sides uses "
                    + "the larger of the two deficits.")),
                Paragraph(Text("Sum the resulting deficits over the selected thresholds. The upper "
                    + "bound counts each ordinary cell with odd mass once per positive deficit at "
                    + "a threshold strictly above the complementary column weight and at most the "
                    + "row weight. At each threshold the odd margins ensure enough such cells to "
                    + "pay the selected deficit. The two sides use the same eligible cells."))),
            DescribeRole.Theorem))));
}
