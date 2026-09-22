using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class NestedGridEntropyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/NestedGridEntropy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A legal binary refinement history imposes an entropy budget beyond the static averaging lower bound.",
        H("Nested Grid Entropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nested-grid-finite-entropy-budget"),
                DeclarationHandle.Create(Prefix + "binary_refinement_entropy_budget"),
                H("Finite resolution cost with explicit refinement losses"),
                StatementSource.FromAuthor(BudgetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The initial cell list is [1]. At each step an actual listed parent a+b is replaced by two positive children a and b, leaving the other cells unchanged. From these identities the proof derives positive unit total mass at every stage, the exact entropy increment, and a terminal entropy lower bound from the maximal-cell cap. Each nonnegative loss equals the cost of splitting below the cap plus the binary-entropy deficit of the split ratio. The theorem bounds final log resolution plus cumulative loss by log(2) times the sum of past caps. The ordinary consumer gives the sharp 1/log(2)^2 sequential error factor for the previously derived two-moment grid loss using the classical Niederreiter logarithmic construction. The sequence theorem and the full grid identification are not claimed as kernel-checked by this declaration."))),
                DescribeRole.Theorem))));

    private static Formula I(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula SumTo(Formula n, Formula value) =>
        Seq(Sum, Underscore, Grp(F.Id("k"), Lt, n), Sp, value);

    private static Formula BudgetFormula()
    {
        var k = F.Id("k"); var n = F.Id("n");
        var a = I(F.Id("a"), k); var b = I(F.Id("b"), k);
        var cap = I(F.Id("c"), k); var loss = I(DeltaLower, k);
        var cells = I(F.Id("C"), k); var next = I(F.Id("C"), Seq(k, Plus, D(1)));
        var before = I(F.Id("B"), k); var after = I(F.Id("A"), k);
        var parent = Seq(a, Plus, b);
        var lossDefinition = Seq(
            loss, Sp, Colon, Eq, Sp,
            Open, cap, Minus, Open, parent, Close, Close, Call("log", D(2)),
            Plus, Open, parent, Close,
            Open, Call("log", D(2)), Minus,
                Call("H", Seq(Frac, Grp(a), Grp(parent))), Close);
        return Disp(Seq(
            Forall, Sp, F.Id("C"), Comma, F.Id("B"), Comma, F.Id("A"), Colon, Sp,
                Mathbb, Grp(F.Id("N")), Sp, To, Sp,
                Call("List", Seq(Mathbb, Grp(F.Id("R")))),
                Comma, Sp,
            Forall, Sp, F.Id("a"), Comma, F.Id("b"), Comma, F.Id("c"), Colon, Sp,
                Mathbb, Grp(F.Id("N")), Sp, To, Sp, Mathbb, Grp(F.Id("R")),
                Comma, Sp,
            Call("C", D(0)), Sp, Eq, Sp, OpenBracket, D(1), CloseBracket,
                Sp, Land, Sp,
            Open, Forall, Sp, k, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Open, D(0), Sp, Lt, Sp, a, Sp, Land, Sp, D(0), Sp, Lt, Sp, b, Close,
                Sp, Land, Sp,
            cells, Sp, Eq, Sp, before, Plus, Plus,
                OpenBracket, parent, CloseBracket, Plus, Plus, after, Sp, Land, Sp,
            next, Sp, Eq, Sp, before, Plus, Plus,
                OpenBracket, a, Comma, b, CloseBracket, Plus, Plus, after, Sp, Land, Sp,
            Open, Forall, Sp, F.Id("x"), Sp, InMacro, Sp, cells, Comma, Sp,
                F.Id("x"), Sp, Le, Sp, cap, Close, Close,
            Sp, Longrightarrow, Sp,
            F.Text, Grp(F.Id("let"), Sp), Sp, lossDefinition, Semi, Sp,
            Open, Forall, Sp, k, Comma, Sp, D(0), Sp, Le, Sp, loss, Close,
                Sp, Land, Sp,
            Open, Forall, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                Call("log", Seq(Frac, Grp(D(1)), Grp(I(F.Id("c"), n)))),
                Plus, SumTo(n, I(DeltaLower, k)), Sp, Le, Sp,
                Call("log", D(2)), SumTo(n, I(F.Id("c"), k)), Close));
    }
}
