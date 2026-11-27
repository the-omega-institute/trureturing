using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.OrderedTrees;

internal sealed class LeafGapCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered leaf-gap compositions enumerate the actual trees at every size.",
        H("Counting Ordered Leaf-Gap Decorations"),
        Blocks(Describe.Lean(
            DescribeId.Create("ordered-leaf-gap-count"),
            DeclarationHandle.Create("D5/S3/Combinatorics/OrderedTrees/LeafGapCount.count_eq_sum"),
            H("The actual count is the sum over skeleton sizes"),
            StatementSource.FromAuthor(CountFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For each natural index n, a(n) is the finite cardinality of ordered rooted trees "
                    + "with n vertices and vertex height equal to the number of nonleaf vertices. "
                    + "The sum is empty when n is less than five.")),
                Paragraph(Text(
                    "For each feasible u, the 2u+1 distinct ordered skeletons of size u+3 are "
                    + "decorated by two mandatory terminal leaves and 2u+5 free gaps. The free gap "
                    + "counts have sum n−u−5. Reading gaps in order and inflating them are inverse "
                    + "operations. Weak composition cardinality gives the binomial coefficient for "
                    + "each skeleton. The two arm orientations share only the equal-arm case, which "
                    + "the skeleton list counts once."))),
            DescribeRole.Theorem))));

    private static Formula CountFormula()
    {
        var n = Id("n");
        var u = Id("u");
        var sum = new Formula.Subscript(Sum, Seq(D(0), Sp, Leq, Sp, u, Sp, Lt, Sp, n, Minus, D(4)));
        return Disp(Seq(Id("a"), Open, n, Close, Sp, Eq, Sp, sum, Sp,
            Open, D(2), u, Plus, D(1), Close,
            new Formula.FunctionCall(FormulaIdentifier.Create("choose"),
                [Seq(n, Plus, u, Minus, D(1)), Seq(D(2), u, Plus, D(4))])));
    }
}
