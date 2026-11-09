using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class CopelandA131758PolynomialContentRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/copeland2008a131758");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At n=8 the complete coefficient row has content 1, but the proposed count is 2.",
        H("Copeland's A131758 polynomial content conjecture"),
        Blocks(
            Node("coefficients", "The source coefficient formula", CoefficientFormula(),
                "OEIS A131758, FORMULA (unpaginated), states verbatim: "
                + "\"a(n,m) = (-1)^n*n!*Sum_{k=0..m} (-1)^k*C(n+1,k)*Lag(n, m-k+1).\" "
                + "COMMENTS: \"Lag(n,x) is a Laguerre polynomial and T(n,t) is a Touchard / Bell / exponential polynomial.\" "
                + "The displayed inner rational sum is the ordinary order-zero Laguerre expansion "
                + "of DLMF 18.5.12 at α=0. Indices n,m,k,j are natural numbers; "
                + "Nat.sub is truncated natural subtraction, and k≤m throughout the outer sum. "
                + "Rational division is by j!, which is nonzero.",
                "a", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("polynomial", "The complete polynomial", PolynomialFormula(),
                "OEIS A131758, COMMENTS (unpaginated), states verbatim: "
                + "\"The P(n,t) are related to the Laguerre polynomials through\n"
                + "  P(n,t) = (-1)^n n! [ (1-t)^(n+1)} ] Sum_{k>=0} [ (t^k*Lag(n,k+1) ] = Sum_{m=0..n} a(n,m) * t^m\" "
                + "P n is the polynomial over ℚ containing all n+1 displayed coefficients.",
                "P", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("integer-row", "Integer realization of a complete row", RowFormula(),
                "A row has domain Fin (n+1), including indices zero and n. "
                + "Each integer coordinate, cast into ℚ, equals its source coefficient.",
                "IsSourceRow", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("content", "Nonnegative coefficient content", ContentFormula(),
                "The content is the finite gcd of the absolute values of all integer coordinates. "
                + "The gcd of an all-zero row is zero.",
                "rowContent", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("divisor-count", "Divisors no larger than the square root", DivisorFormula(),
                "OEIS A038548, NAME (unpaginated), states verbatim: "
                + "\"Number of divisors of n that are at most sqrt(n).\" "
                + "Nat.divisors contains positive divisors for positive n; d*d≤n expresses "
                + "the square-root bound. Nat.divisors 0 is empty, and D 0 is not asserted below.",
                "D", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Copeland's content assertion", Disp(Iff(F.Id("claim"), ClaimBody())),
                "OEIS A131758, COMMENTS, revision 48 (unpaginated), states verbatim: "
                + "\"Conjecture for the polynomial array:\n"
                + "The greatest common divisor of the coefficients of each polynomial is given by A060872(n)/n or, equivalently, by A038548(n).\" "
                + "The first conjunct asserts integer realizations at every n≥0. The second "
                + "quantifies over every realization and every n≥1, matching the offset of "
                + "A038548. The gcd always uses all n+1 coordinates of that same row.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The content assertion is false", Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "At n=8 the integer row supplied by the existence assertion must begin "
                + "6209, −41417. Their coprimality forces the gcd of the complete nine-coordinate "
                + "row to equal 1. The proposed divisor count D 8 equals 2, a contradiction. "
                + "The proof uses only propext, Classical.choice and Quot.sound. It does not "
                + "prove an infinite family or a replacement content formula.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("copeland-a131758"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("copeland-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks([.. prose.Split('\n').Select(static line => Paragraph(Text(line)))]), role, resolution);

    private static Formula CoefficientFormula()
    {
        var n = F.Id("n"); var m = F.Id("m"); var k = F.Id("k"); var j = F.Id("j");
        var x = Cast(Add(QualifiedCall("Nat", "sub", m, k), D(1)), Rationals());
        var inner = SumRange("j", Add(n, D(1)), new Formula.Fraction(
            Multiply(Multiply(Power(Cast(NegativeOne(), Rationals()), j),
                Cast(QualifiedCall("Nat", "choose", n, j), Rationals())), Power(x, j)),
            Cast(QualifiedCall("Nat", "factorial", j), Rationals())));
        var outer = SumRange("k", Add(m, D(1)), Multiply(
            Multiply(Power(Cast(NegativeOne(), Rationals()), k),
                Cast(QualifiedCall("Nat", "choose", Add(n, D(1)), k), Rationals())),
            Parenthesized(inner)));
        return Disp(All("n", Naturals(), All("m", Naturals(), Equal(Call("a", n, m),
            Multiply(Multiply(Power(Cast(NegativeOne(), Rationals()), n),
                Cast(QualifiedCall("Nat", "factorial", n), Rationals())), Parenthesized(outer))))));
    }

    private static Formula PolynomialFormula()
    {
        var n = F.Id("n"); var m = F.Id("m");
        return Disp(All("n", Naturals(), Equal(Call("P", n), SumRange("m", Add(n, D(1)),
            QualifiedCall("Polynomial", "monomial", m, Call("a", n, m))))));
    }

    private static Formula RowFormula()
    {
        var n = F.Id("n"); var row = F.Id("row"); var m = F.Id("m");
        return Disp(All("n", Naturals(), All("row", RowType(n),
            Iff(Call("IsSourceRow", n, row), All("m", FinType(n),
                Equal(Cast(Call("row", m), Rationals()), Call("a", n, Call("val", m))))))));
    }

    private static Formula ContentFormula()
    {
        var n = F.Id("n"); var row = F.Id("row"); var m = F.Id("m");
        return Disp(All("n", Naturals(), All("row", RowType(n), Equal(Call("rowContent", row),
            QualifiedCall("Finset", "gcd", Cast(Qualified("Finset", "univ"), Call("Finset", FinType(n))),
                LambdaFormula("m", FinType(n), QualifiedCall("Int", "natAbs", Call("row", m))))))));
    }

    private static Formula DivisorFormula()
    {
        var n = F.Id("n"); var d = F.Id("d");
        return Disp(All("n", Naturals(), Equal(Call("D", n), QualifiedCall("Finset", "card",
            QualifiedCall("Finset", "filter", LambdaFormula("d", Naturals(),
                LessEqual(Multiply(d, d), n)), QualifiedCall("Nat", "divisors", n))))));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n"); var row = F.Id("row");
        return And(All("n", Naturals(), ExistsFormula("row", RowType(n), Call("IsSourceRow", n, row))),
            All("n", Naturals(), ImpliesFormula(LessEqual(D(1), n), All("row", RowType(n),
                ImpliesFormula(Call("IsSourceRow", n, row), Equal(Call("rowContent", row), Call("D", n)))))));
    }

    private static Formula SumRange(string name, Formula bound, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Sp, InMacro, Sp, QualifiedCall("Finset", "range", bound)),
            Sp, body);
    private static Formula LambdaFormula(string name, Formula type, Formula body) =>
        Parenthesized(Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)),
            Sp, Mapsto, Sp, body));
    private static Formula RowType(Formula n) => Seq(FinType(n), Sp, To, Sp, Integers());
    private static Formula FinType(Formula n) => Call("Fin", Add(n, D(1)));
    private static Formula Naturals() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Rationals() => new Formula.NamedConstant(FormulaIdentifier.Create("Rat"));
    private static Formula Integers() => new Formula.NamedConstant(FormulaIdentifier.Create("Int"));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsFormula(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot,
        Operatorname, Grp(F.Id(name)));
    private static Formula QualifiedCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula NegativeOne() => Seq(Minus, D(1));
    private static Formula Power(Formula x, Formula n) => new Formula.Power(x, n);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Multiply(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula LessEqual(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula ImpliesFormula(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
}
