using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class KurkovReversedQBellRowPolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/KurkovReversedQBellRowPolynomial.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/kurkov2025a126347");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kurkov's triangular recurrence produces the reversed q-Bell row polynomials.",
        H("Kurkov's Reversed q-Bell Row Polynomials"),
        Blocks(
            Paragraph(Text(
                "All indices are natural numbers, including zero, and all polynomials lie "
                    + "in Z[X]. The expression binom(n,k) is the natural binomial "
                    + "coefficient cast to an integer constant polynomial. A sum with "
                    + "upper index k-1 ranges over j=0,...,k-1 and is empty when k=0. "
                    + "The reversal operator reflects coefficients about the natural degree.")),
            Node(
                "qBell",
                "The q-Bell row polynomials",
                QBellFormula(),
                "The initial row is one. Wagner's recurrence forms row n+1 from all rows "
                    + "through n, weighted by binom(n,k) X^k. These are the row "
                    + "polynomials whose coefficients form OEIS A126347.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "kurkovR",
                "Kurkov's triangular recurrence",
                KurkovFormula(),
                "Row zero is one at column zero and zero at later columns. Every later "
                    + "entry adds the preceding diagonal to X^(n+1) times the prefix of "
                    + "row n. On the diagonal of row n+1 that prefix only reads columns "
                    + "j<=n, so the row-zero totalization cannot affect the theorem.",
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node(
                "result",
                "Kurkov's reversed-row identity",
                ResultFormula(),
                "For every n, the diagonal entry R(n,n) is the coefficient reversal of "
                    + "qBell(n+1). The q-Bell polynomial is monic of degree binom(n+1,2), "
                    + "so natural-degree reversal agrees with reversal of the fixed-length "
                    + "OEIS row. A Pascal expansion of the R-prefix sums supplies the "
                    + "binomial convolution used by Wagner's recurrence.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
            DescribeId.Create("a126347-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Universal(Formula variables, Formula body) =>
        Seq(Forall, Sp, variables, Sp, InMacro, Sp, Naturals(), Comma, Sp, body);
    private static Formula FiniteSum(Formula index, Formula upper, Formula summand) =>
        Seq(new Formula.Subscript(F.Sum, Equal(index, D(0))),
            Caret, Grp(upper), Sp, Parenthesized(summand));

    private static Formula QBellFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), x = F.Id("X");
        Formula summand = Multiply(
            Multiply(Call("binom", n, k), Call("qBell", k)),
            Power(x, k));
        return Disp(new Formula.Aligned([
            Equal(Call("qBell", D(0)), D(1)),
            Universal(n, Equal(
                Call("qBell", Parenthesized(Add(n, D(1)))),
                FiniteSum(k, n, summand))),
        ]));
    }

    private static Formula KurkovFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), j = F.Id("j"), x = F.Id("X");
        Formula prefix = FiniteSum(j, Subtract(k, D(1)), Call("R", n, j));
        Formula step = Add(
            Call("R", n, n),
            Multiply(Power(x, Parenthesized(Add(n, D(1)))), Parenthesized(prefix)));
        return Disp(new Formula.Aligned([
            Equal(Call("R", D(0), D(0)), D(1)),
            Universal(k, Equal(
                Call("R", D(0), Parenthesized(Add(k, D(1)))), D(0))),
            Universal(Seq(n, Comma, Sp, k), Equal(
                Call("R", Parenthesized(Add(n, D(1))), k), step)),
        ]));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        return Disp(Universal(n, Equal(
            Call("R", n, n),
            Call("reverse", Call("qBell", Parenthesized(Add(n, D(1))))))));
    }
}
