using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class BarryTriangleRowSumsOddDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ArithSums/BarryTriangleRowSumsOdd.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/barry2005a105595");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every row sum of the A105594 triangle is odd.",
        H("Barry's A105595 row-sum conjecture"),
        Blocks(
            Node(
                "rowEntry",
                "The A105594 triangle entry",
                RowEntryFormula(),
                "For fixed n and k, sum over j from zero through n the absolute "
                    + "Moebius value of binomial(n,j), multiplied by the parity of "
                    + "binomial(j,k), and reduce the resulting inner sum modulo two.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "rowSum",
                "The A105595 row sum",
                RowSumFormula(),
                "The nth term is the sum of rowEntry(n,k) over k from zero through n.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "result",
                "Every row sum is odd",
                ResultFormula(),
                "Each already reduced inner sum is first cast into integers modulo two, "
                    + "where reduction modulo two preserves its value, and the finite sums "
                    + "may then be interchanged. For a fixed j, the binomial row through n "
                    + "equals two to the power j because terms with k greater than j vanish. "
                    + "Modulo two only j=0 remains, and its coefficient is the absolute "
                    + "Moebius value at one, which equals one.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a105595-barry-triangle-row-sums-odd"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("a105595-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula RowEntryFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var j = F.Id("j");
        var chooseNj = Call("binomial", n, j);
        var chooseJk = Call("binomial", j, k);
        var coefficient = new Formula.Absolute(
            Seq(Mu, Parenthesized(chooseNj)));
        var parity = Parenthesized(new Formula.Modulo(chooseJk, D(2)));
        var summand = new Formula.Binary(
            coefficient,
            FormulaBinaryOperator.Multiply,
            parity);
        var innerSum = BoundedSum(j, n, summand);
        return Universal(["n", "k"], Equal(
            Call("rowEntry", n, k),
            new Formula.Modulo(Parenthesized(innerSum), D(2))));
    }

    private static Formula RowSumFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        return Universal(["n"], Equal(
            Call("rowSum", n),
            BoundedSum(k, n, Call("rowEntry", n, k))));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        return Universal(["n"], Call("Odd", Call("rowSum", n)));
    }

    private static Formula BoundedSum(Formula index, Formula upper, Formula summand)
    {
        var lower = Seq(index, Sp, Eq, Sp, D(0));
        return Seq(
            Sum,
            Underscore,
            new Formula.LatexGroup([lower]),
            Caret,
            new Formula.LatexGroup([upper]),
            Sp,
            summand);
    }

    private static Formula Universal(string[] names, Formula body) => Disp(
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(
                FormulaIdentifier.Create(name), Naturals()))],
            body));

    private static Formula Naturals() =>
        Seq(Mathbb, new Formula.LatexGroup([F.Id("N")]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
