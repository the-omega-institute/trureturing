using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.UnorderedTrees;

internal sealed class ForkCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two bounded binomial sums give the actual unordered rooted-tree count.",
        H("Counting normalized fork decorations"),
        Blocks(Describe.Lean(
            DescribeId.Create("unordered-count-by-arms"),
            DeclarationHandle.Create("D5/S3/Combinatorics/UnorderedTrees/ForkCount.count_by_arms"),
            H("The equal-arm and unequal-arm contributions"),
            StatementSource.FromAuthor(CountFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The sum indices are natural numbers. In the equal-arm case m is the "
                    + "smaller tip offset. The difference between the tip offsets and the "
                    + "b+1 spine counts are b+2 free slots of total n−b−5−2m. "
                    + "The resulting binomial counts also include the diagonal pair.")),
                Paragraph(Text(
                    "With unequal arms and u=b+c, there are u choices of positive c. "
                    + "The u+1 spine counts and two tip offsets give u+3 free slots "
                    + "of total n−u−5. The Lean unequal-arm sum uses v=u−1 and range(n−5). "
                    + "All subtractions inside the binomials are taken on the indicated "
                    + "feasible ranges, including empty ranges at small n."))),
            DescribeRole.Theorem))));

    private static Formula CountFormula()
    {
        var n = F.Id("n");
        var b = F.Id("b");
        var m = F.Id("m");
        var u = F.Id("u");
        var eq = new Formula.Subscript(Sum, Seq(b, Comma, m, Sp, Colon, Sp,
            b, Plus, D(5), Plus, D(2), m, Sp, Leq, Sp, n));
        var uneq = new Formula.Subscript(Sum, Seq(D(1), Sp, Leq, Sp, u, Sp, Leq, Sp, n, Minus, D(5)));
        return Disp(Seq(Forall, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            F.Id("a"), Open, n, Close, Sp, Eq, Sp, eq, Sp,
            Choose(Seq(n, Minus, D(4), Minus, D(2), m), Seq(b, Plus, D(1))),
            Sp, Plus, Sp, uneq, Sp, u, Choose(Seq(n, Minus, D(3)), Seq(u, Plus, D(2)))));
    }

    private static Formula Choose(Formula n, Formula k) =>
        new Formula.FunctionCall(FormulaIdentifier.Create("choose"), [n, k]);
}
