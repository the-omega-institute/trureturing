using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class SchulteGcdQuotientRowSumConvolutionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ArithSums/SchulteGcdQuotientRowSumConvolution.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/schulte2022a350900");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schulte's A350900 row sum is a Dirichlet convolution of two totient sums.",
        H("Schulte's gcd-quotient row-sum convolution"),
        Blocks(
            Paragraph(Text(
                "All indices and values are natural numbers, including zero. The "
                    + "symbol n is the row number, i and k are the summation indices "
                    + "from one through n, and d and e are divisors. gcd denotes the "
                    + "greatest common divisor, phi is Euler's totient function, and "
                    + "rowSum(n) is the sum of the entries in row n. The slash denotes "
                    + "natural-number division: the row summands and divisions by "
                    + "divisors are exact quotients. Only the conjectured row-sum "
                    + "convolution is established. The separate statement about "
                    + "arbitrary arithmetic functions is not addressed.")),
            Node(
                "rowSum",
                "The A350900 row sum",
                RowSumFormula(),
                "For each n, the outer sum runs over i=1 through n and the inner "
                    + "sum over k=1 through n. Each term is gcd(i,n) divided "
                    + "exactly by gcd(gcd(i,k),n). The sums are empty at n=0.",
                DescribeRole.Definition),
            Node(
                "result",
                "Schulte's row-sum identity",
                ResultFormula(),
                "For every positive n, the row sum equals the Dirichlet "
                    + "convolution of d times phi(d) with the divisor sum of e "
                    + "times phi(e). Fixing i with g=gcd(i,n), the inner sum "
                    + "over k is (n/g) times the sum of f times phi(f) over "
                    + "divisors f of g; this follows by grouping k by gcd(g,k). "
                    + "The outer sum groups i by g, with phi(n/g) values for "
                    + "each g, and reindexes complementary divisors by d=n/g.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a350900-schulte-gcd-quotient-row-sum-convolution"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(
            DescribeId.Create("a350900-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula RowSumFormula()
    {
        var n = F.Id("n");
        var i = F.Id("i");
        var k = F.Id("k");
        var term = NaturalDivide(
            Call("gcd", i, n), Call("gcd", Call("gcd", i, k), n));
        return Universal(Equal(
            Call("rowSum", n), RangeSum(i, n, RangeSum(k, n, term))));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var e = F.Id("e");
        var divisorSum = DivisorSum(e, NaturalDivide(n, d),
            Multiply(e, Call("phi", e)));
        var convolution = DivisorSum(d, n,
            Multiply(Multiply(d, Call("phi", d)), divisorSum));
        return Universal(Implies(
            Parenthesized(Less(D(0), n)),
            Parenthesized(Equal(Call("rowSum", n), convolution))));
    }

    private static Formula Universal(Formula body) => Disp(new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), Naturals(), body));

    private static Formula RangeSum(Formula index, Formula n, Formula summand) =>
        Seq(new Formula.Subscript(F.Sum,
            Seq(index, Sp, Eq, Sp, D(1), Dot, Dot, n)), Sp, summand);

    private static Formula DivisorSum(Formula index, Formula n, Formula summand) =>
        Seq(new Formula.Subscript(F.Sum, Seq(index, Sp, Mid, Sp, n)),
            Sp, summand);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula NaturalDivide(Formula numerator, Formula denominator) =>
        Seq(Parenthesized(numerator), Sp, Slash, Sp, Parenthesized(denominator));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
