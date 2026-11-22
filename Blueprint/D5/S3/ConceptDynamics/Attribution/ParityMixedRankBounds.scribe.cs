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
        return Disp(new Formula.Logic(
            Call("OddUniformMarginsAndDisjointCuts", n, k, rows, columns, table, flags),
            FormulaLogicOperator.Implies,
            Seq(Call("MixedRankDeficits", n, k, rows, columns), Sp, Le, Sp,
                Call("IntersectionCount", n, table, flags))));
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
                    + "natural-number thresholds are disjoint, and every threshold is at most "
                    + "n minus 2 in natural-number subtraction. Some full-row flag is positive "
                    + "and at most its corresponding mass.")),
                Paragraph(Text("The score multiplies the intersection size of each ordinary cell "
                    + "by its mass modulo two. Each full-row cell instead uses its flag.")),
                Paragraph(Text("The bound starts with one. For each r in R, add the positive part "
                    + "of one plus the number of ordinary even rows of weight at least r, minus "
                    + "k times the number of odd columns of weight at most n minus r. For each "
                    + "r in C, add the positive part of one plus the number of odd columns of "
                    + "weight greater than n minus r, minus k times one plus the number of even "
                    + "rows of weight below r. The extra row in that capacity estimate is the "
                    + "full row.")),
                Paragraph(Text("A charged ordinary cell assigns each selected threshold to a "
                    + "distinct position in the integer interval from n minus the column weight, "
                    + "excluded, to the row weight, included. The positive full-row flag "
                    + "covers a baseline unit and the thresholds above the lower endpoint for "
                    + "its own column. For other thresholds, the mass at that flag improves "
                    + "the capacity estimate by one."))),
            DescribeRole.Theorem))));
}
