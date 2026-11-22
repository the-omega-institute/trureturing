using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParityMixedRankBoundsDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        var table = F.Id("m");
        var rows = F.Id("R");
        var columns = F.Id("C");
        return Disp(new Formula.Logic(
            Seq(Call("MismatchCount", table, rows, columns), Sp, Le, Sp,
                Call("ChargedOddCellScore", table, rows, columns)),
            FormulaLogicOperator.And,
            Call("CellChargesBoundedByOrdinaryIntersection", table, rows, columns)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Combine exact row and column parity mismatches at selected rank thresholds.",
        H("Combine parity mismatches on row and column cuts"),
        Blocks(Describe.Lean(
            DescribeId.Create("mixed-parity-rank-deficits"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Attribution/ParityMixedRankBounds.mixed_rank_lower"),
            H("Mixed rank deficits for arbitrary margins"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Rows are even subsets of the coordinates and columns are odd "
                    + "subsets. Fix a distinguished row. The table entries are natural numbers. "
                    + "Row and column margins can have either parity.")),
                Paragraph(Text("At a selected row threshold, consider rows of at least that "
                    + "weight outside the distinguished row. Count those whose total mass and "
                    + "mass in columns at or below the complementary rank have different parity. "
                    + "At a selected column threshold, consider columns above the complementary "
                    + "rank. Count those whose total mass and mass received from the distinguished "
                    + "row and lower-weight rows have different parity.")),
                Paragraph(Text("Use the larger count at each threshold and choose rows in a tie. "
                    + "Only odd cells on the chosen side, incident to a counted row or column "
                    + "and lying outside its free block, contribute to the score. The sum of the "
                    + "larger counts is at most this score. The distinguished row contributes "
                    + "zero. For every other cell, its contributing thresholds lie strictly "
                    + "above the complementary column rank and at most the row weight, so their "
                    + "number is at most the size of the row and column intersection."))),
            DescribeRole.Theorem))));
}
