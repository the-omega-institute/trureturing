using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class SchulteShiftedProductGcdRowSumConvolutionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ArithSums/SchulteShiftedProductGcdRowSumConvolution.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/schulte2022a347293");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schulte's shifted-product gcd row sum equals a divisor convolution of squares and squared totients.",
        H("OEIS A347293 row-sum convolution"),
        Blocks(
            Node(
                "rowSum",
                "The shifted-product gcd row sum",
                RowSumFormula(),
                "The two range sums run over x and y from zero through n minus one. "
                    + "They are the OEIS triangle's row sum after the index changes "
                    + "x=i-1 and y=k-1.",
                DescribeRole.Definition),
            Node(
                "result",
                "The square and squared-totient convolution",
                ResultFormula(),
                "For each divisor d of n, reduction modulo d identifies the pairs "
                    + "with d dividing 1+xy with a unit and its unique negative inverse. "
                    + "There are totient(d) residue pairs and each has (n/d)^2 lifts. "
                    + "Expanding each gcd by the totient divisor sum and reindexing "
                    + "complementary divisors gives the displayed convolution.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a347293-schulte-shifted-product-gcd-row-sum-convolution"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a347293-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name),
        H(title),
        StatementSource.FromAuthor(formula),
        AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))),
        role,
        claim);

    private static Formula RowSumFormula()
    {
        var n = F.Id("n");
        var x = F.Id("x");
        var y = F.Id("y");
        var product = Multiply(x, y);
        var summand = Call("gcd", Add(D(1), product), n);
        var inner = Seq(
            new Formula.Subscript(Sum, Seq(y, Sp, InMacro, Sp, Call("range", n))),
            Sp,
            summand);
        var outer = Seq(
            new Formula.Subscript(Sum, Seq(x, Sp, InMacro, Sp, Call("range", n))),
            Sp,
            Parenthesized(inner));
        return Universal("n", Equal(Call("rowSum", n), outer));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var quotient = Seq(n, Sp, Slash, Sp, d);
        var summand = Multiply(
            new Formula.Power(d, D(2)),
            new Formula.Power(Call("totient", quotient), D(2)));
        var divisorSum = Seq(
            new Formula.Subscript(Sum, Seq(d, Sp, InMacro, Sp, Call("divisors", n))),
            Sp,
            summand);
        var conclusion = Equal(Call("rowSum", n), divisorSum);
        return Universal("n", new Formula.Logic(
            Parenthesized(Greater(n, D(0))),
            FormulaLogicOperator.Implies,
            Parenthesized(conclusion)));
    }

    private static Formula Universal(string name, Formula body) => Disp(
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name),
            Naturals(),
            body));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Greater(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);
}
