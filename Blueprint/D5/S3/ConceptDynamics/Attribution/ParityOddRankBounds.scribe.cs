using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParityOddRankBoundsDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var m = F.Id("m");
        var b = F.Id("b");
        var first = Call("PositivePart", Seq(Add(n, D(1)), Sp, Minus, Sp, Call("Twice", k)));
        var second = Call("PositivePart", Seq(Add(Call("Choose", n, D(2)), D(1)),
            Sp, Minus, Sp, Mul(n, k)));
        var bound = Seq(Add(Add(D(1), first), second), Sp, Le, Sp,
            Call("IntersectionCount", n, m, b));
        return Disp(new Formula.Logic(Call("OddUniformMargins", n, k, m, b),
            FormulaLogicOperator.Implies, bound));
    }

    private static Formula WeightedStatement()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var m = F.Id("m");
        var b = F.Id("b");
        var first = Call("PositivePart", Seq(n, Sp, Minus, Sp, Call("TopMass", m)));
        var second = Call("PositivePart", Seq(Call("Choose", n, D(2)), Sp, Minus, Sp, Call("HighSingletonMass", m)));
        var bound = Seq(Add(Add(Call("FlagCost", b), first), second), Sp, Le, Sp,
            Call("IntersectionCount", n, m, b));
        return Disp(new Formula.Logic(Call("OddMargins", n, k, m, b),
            FormulaLogicOperator.Implies, bound));
    }

    private static Formula Mul(Formula left, Formula right) =>
        Seq(left, Sp, Cdot, Sp, right);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lower bound from high ranks in the odd uniform parity matrix.",
        H("High-rank constraints at odd parity budgets"),
        Blocks(Describe.Lean(
            DescribeId.Create("rank-deficits-with-full-row-masses"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Attribution/ParityOddRankBounds.weighted_rank_deficits_le_intersections"),
            H("The two exceptional masses determine the rank deficits"),
            StatementSource.FromAuthor(WeightedStatement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For OddMargins, the dimension n is even and at least six. "
                    + "The natural-number matrix m on even and odd subsets of Fin(n) has "
                    + "every row and column sum equal to the odd number k. The flags b are "
                    + "arbitrary natural numbers on the odd subsets.")),
                Paragraph(Text("TopMass sums the zero and full rows on columns of size n minus one. "
                    + "HighSingletonMass sums entries in rows of size n minus two and singleton columns. "
                    + "FlagCost sums each flag times its column size. IntersectionCount "
                    + "uses the flags in the full row and entry parity elsewhere, weighted "
                    + "by intersection size. PositivePart truncates a negative difference "
                    + "to zero."))),
            DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("odd-margin-intersection-lower-bound"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Attribution/ParityOddRankBounds.fixed_from_odd_margins"),
            H("Two rank constraints bound the total weighted intersection count"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The dimension n is even and at least six, and k is odd. "
                    + "The natural-number matrix m is indexed by even and odd subsets of Fin(n) and has "
                    + "every row and column sum equal to k. The natural-number vector b is "
                    + "bounded by the all-ones row, and positive at some column. "
                    + "These are the conditions denoted by OddUniformMargins.")),
                Paragraph(Text("IntersectionCount weights each cell by the size of the "
                    + "intersection of its two subsets and by its multiplicity modulo two. "
                    + "In the all-ones row it uses b in place of the multiplicity modulo two. "
                    + "PositivePart truncates a negative difference to zero.")),
                Paragraph(Text("Columns of size n minus one can use the zero and all-ones "
                    + "rows to meet their parity demand. Rows of size n minus two can "
                    + "use singleton columns. The remaining demands each force a positive "
                    + "intersection. Any cell used by both demands has intersection size "
                    + "at least n minus three. A positive entry of b in a singleton column "
                    + "consumes capacity in both counts. A positive entry elsewhere "
                    + "contributes at least three to the bound directly."))),
            DescribeRole.Theorem))));
}
