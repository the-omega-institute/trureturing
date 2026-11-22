using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParityMixedRankBoundsDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var rows = F.Id("R");
        var columns = F.Id("C");
        var table = F.Id("m");
        var flags = F.Id("b");
        var column = F.Id("q");
        return Disp(new Formula.Logic(
            Call("OddUniformMarginsAndDisjointCuts", n, k, rows, columns, table, column),
            FormulaLogicOperator.Implies,
            Seq(Call("FullRowScore", n, flags), Sp, Plus, Sp,
                Call("MixedRankDeficits", n, k, rows, columns), Sp, Le, Sp,
                Call("IntervalWeightedCount", n, table, flags), Sp, Plus, Sp,
                Call("ChargedPositiveDeficitCount", n, k, rows, columns, column))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatible row and column rank deficits for an odd-margin parity table.",
        H("Combine row and column cuts on one parity table"),
        Blocks(Describe.Lean(
            DescribeId.Create("mixed-odd-parity-rank-deficits"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Attribution/ParityMixedRankBounds.mixed_rank_lower"),
            H("Mixed rank deficits under odd uniform margins"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The dimension n is even. Each row and column of the natural-number "
                    + "table has the same odd marginal k. Rows are all even subsets of the "
                    + "coordinates and columns are all odd subsets. The finite sets R and C of "
                    + "natural-number thresholds are disjoint. The chosen column q has positive "
                    + "mass in the full row.")),
                Paragraph(Text("Each ordinary cell contributes its rank interval length times "
                    + "its mass modulo two. Each full-row cell contributes its column weight "
                    + "times its flag. Differences between natural numbers are truncated at zero.")),
                Paragraph(Text("The bound starts with the full-row score. For each r in R, add the "
                    + "positive part of one plus the number of ordinary even rows of weight at least r, minus "
                    + "k times the number of odd columns of weight at most n minus r. For each "
                    + "r in C, add the positive part of one plus the number of odd columns of "
                    + "weight greater than n minus r, minus k times the quantity one plus the number of even "
                    + "rows of weight below r. The additional allowance in that estimate "
                    + "accounts for the full row.")),
                Paragraph(Text("For each ordinary cell, assign every threshold that charges that cell to a "
                    + "distinct position in the integer interval from n minus the column weight, "
                    + "excluded, to the row weight, included. Its length is the intersection "
                    + "size minus the number of coordinates missed by both profiles, using "
                    + "natural-number subtraction. Count a selected threshold on the right-hand "
                    + "side when its deficit is positive and q has weight greater than n minus r. "
                    + "For a positive deficit at any other threshold, the mass in q improves "
                    + "the capacity estimate by one."))),
            DescribeRole.Theorem))));
}
