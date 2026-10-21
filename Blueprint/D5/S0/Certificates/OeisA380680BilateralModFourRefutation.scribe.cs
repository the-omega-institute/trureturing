using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class OeisA380680BilateralModFourRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/OeisA380680BilateralModFourRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2025a380680");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's square-residue conjecture for OEIS A380680 fails at n = 1.",
        H("The OEIS A380680 Square-Residue Conjecture Is False"),
        Blocks(
            Node("a", "The coefficients of A380680", Disp(CoefficientFormula()),
                "Paul D. Hanna, OEIS A380680, unpaginated Name: \"G.f. A(x) = Sum_{n=-oo..+oo} x^(n^2) * (2 - x^n)^n/(1 - 2*x^n)^n.\" "
                + "Comments: \"The term x^(n^2) * (2 - x^n)^n/(1 - 2*x^n)^n is invariant under sign reversal of n.\" "
                + "Formula (2): \"A(x) = 1 + 2*Sum_{n>=1} x^(n^2) * (2 - x^n)^n/(1 - 2*x^n)^n.\" "
                + "The term at zero is one and opposite indices give equal terms. "
                + "The coefficient at the natural index m is taken in PowerSeries(Q), summing over Finset.Icc 1 m. "
                + "Larger indices contribute zero because the summand contains X^(n^2). "
                + "The inverse is the formal power-series inverse, with denominator constant coefficient one. "
                + "The entry starts at index zero, with coefficients 1, 4, 6.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Hanna's square-residue conjecture",
                Disp(Equal(Named("claim"), Parenthesized(ClaimBody()))),
                "OEIS A380680, unpaginated Comments: \"Conjecture: for n > 0, a(n) == 2 (mod 4) iff n is a square, and a(n) is divisible by 4 when n is nonsquare.\" "
                + "The index n is natural and positive. The integer z equals the rational coefficient a(n) through the integer-to-rational coercion. "
                + "Int.emod z 4 is the integer remainder z % 4. IsSquare n means that n is a product of a natural number with itself. "
                + "Both the residue equivalence and nonsquare divisibility are asserted for that same integer z.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture fails at one",
                Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "The first coefficient is a(1) = 4: only index one contributes, and its quotient has constant coefficient two. "
                + "Since one is a square, the conjecture would require the integer coefficient four to have remainder two modulo four. "
                + "Its remainder is zero, giving a contradiction.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("a380680-" + name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Bound(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));

    private static Formula CoefficientFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n");
        var x = Parenthesized(Seq(Qualified("PowerSeries", "X"), Colon, Sp, Call("PowerSeries", Rationals())));
        var term = Mul(Mul(Power(x, Power(n, D(2))), Power(Subtract(D(2), Power(x, n)), n)),
            Power(Power(Subtract(D(1), Mul(D(2), Power(x, n))), n), Seq(Minus, D(1))));
        var interval = new Formula.Apply(Qualified("Finset", "Icc"), [D(1), m]);
        var sum = Seq(new Formula.Subscript(Sum, Seq(n, Sp, InMacro, Sp, interval)), Sp, Parenthesized(term));
        var coefficient = new Formula.Apply(Qualified("PowerSeries", "coeff"), [m, Add(D(1), Mul(D(2), sum))]);
        return Bound("m", Naturals(), Equal(Call("a", m), coefficient));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), z = F.Id("z");
        var square = Call("IsSquare", n);
        var remainder = new Formula.Apply(Qualified("Int", "emod"), [z, D(4)]);
        var residue = Logic(Equal(remainder, D(2)), FormulaLogicOperator.Iff, square);
        var divisibility = new Formula.Relation(Parenthesized(Seq(D(4), Colon, Sp, Integers())),
            FormulaRelationOperator.Divides, z);
        var nonsquare = Logic(new Formula.Not(square), FormulaLogicOperator.Implies, divisibility);
        var cast = Parenthesized(Seq(z, Colon, Sp, Rationals()));
        var conditions = Logic(Equal(cast, Call("a", n)), FormulaLogicOperator.And,
            Logic(residue, FormulaLogicOperator.And, nonsquare));
        var witness = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("z"), Integers(), conditions);
        return Bound("n", Naturals(), Logic(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n),
            FormulaLogicOperator.Implies, witness));
    }
}
