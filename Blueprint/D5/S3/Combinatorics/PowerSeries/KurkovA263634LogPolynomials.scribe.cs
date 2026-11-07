using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PowerSeries;

internal sealed class KurkovA263634LogPolynomialsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PowerSeries/KurkovA263634LogPolynomials.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/kurkov2025a263634");
    private const string GeneratingQuote = "G.f.: Log(1 + Sum_{i >= 1} x_i*t^i/i!) =  Sum_{n >= 1} L_n(x_1, x_2, ...)*t^n/n!. [Comtet, p. 140, Eq. [5a]. - corrected by _Tom Copeland_, Sep 08 2016]";
    private const string RecursionQuote = "Conjecture: row polynomials are R(n,1) for n > 0 where R(n,k) = R(n-1,k+1) - Sum_{j=1..n-1} binomial(n-2,j-1)*R(j,k)*R(n-j,1) for n > 1, k > 0 with R(1,k) = x_k for k > 0. - _Mikhail Kurkov_, Mar 30 2025";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kurkov's recursion gives every logarithmic polynomial in every positive row.",
        H("The logarithmic-polynomial recursion of OEIS A263634"),
        Blocks(
            Paragraph(Text("The coefficient algebra is MvPolynomial ℕ ℚ. Its indeterminates are indexed by natural numbers; the variable with index zero does not occur in any positive-column recursion. PowerSeries.logOf is the formal logarithm of a series with constant coefficient one. All series and derivatives here are formal; no analytic convergence is assumed.")),
            Node("sourceSeries", "The source exponential series", Eqn(V("sourceSeries"), SourceBody()),
                "OEIS A263634, revision 166, unpaginated FORMULA field: " + GeneratingQuote
                + " The coefficient at zero is one; at positive i it is MvPolynomial.C of the rational inverse of i factorial, multiplied by MvPolynomial.X i. Sorting monomials affects only the printed coefficient list.",
                AssessedProvenance.FromLiterature(Source)),
            Node("IsSourceFamily", "The logarithmic-polynomial family",
                All("L", FamilyType(), IffOf(Call("IsSourceFamily", V("L")), FamilyBody())),
                "OEIS A263634, revision 166, unpaginated FORMULA field: " + GeneratingQuote
                + " The auxiliary value L 0 is zero. Every positive coefficient has the factorial normalization printed in the source.",
                AssessedProvenance.FromLiterature(Source)),
            Node("R", "The recursive array", RecursionBody(),
                "OEIS A263634, revision 166, unpaginated FORMULA field: " + RecursionQuote
                + " In the last equation n = m + 2 and j = r.val + 1. Thus r ranges over Fin (m + 1), the binomial weight is m.choose r.val, and the other row is m - r.val + 1. This subtraction is natural subtraction, with r.val ≤ m. Row zero is extended by zero; column zero is outside the assertion.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Kurkov's complete conjecture", IffOf(V("claim"), ClaimBody()),
                "OEIS A263634, revision 166, unpaginated FORMULA field: " + RecursionQuote
                + " The logarithmic-polynomial family is specified by: " + GeneratingQuote
                + " The assertion includes existence and identifies every family with that generating series at every positive row. The variables remain algebraically independent.",
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "The recursion gives the logarithmic polynomials", ClaimBody(),
                "Put Q k = ((PowerSeries.derivative)^[k] sourceSeries) * PowerSeries.invOfUnit sourceSeries 1 inside the proof. Differentiating its product with sourceSeries gives D(Q k) = Q (k + 1) - Q k * Q 1. The iterated product rule produces exactly the binomial convolution in R. Simultaneous induction over all positive columns identifies R (n + 1) k with the constant coefficient of D^[n](Q k). The formal logarithmic derivative then identifies the first column. Coefficient comparison proves the assertion for every source family, and also constructs such a family.",
                AssessedProvenance.FromRepo(Source), theorem: true))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, bool theorem = false) => Describe.Lean(
        DescribeId.Create("kurkov263634-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
        Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Rat() => Seq(Mathbb, Grp(V("Q")));
    private static Formula PolynomialType() => Call("MvPolynomial", Nat(), Rat());
    private static Formula FamilyType() => new Formula.TypeArrow(Nat(), PolynomialType());
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsAt(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Fn(string name, Formula type, Formula body) => Seq(V("fun"), Sp, Cast(V(name), type), Sp, Mapsto, Sp, body);
    private static Formula Normalized(Formula n, Formula value) => Mul(
        App(Q("MvPolynomial", "C"), App(Q("Inv", "inv"), Cast(App(Q("Nat", "factorial"), n), Rat()))), value);
    private static Formula SeriesOfFamily() => App(Q("PowerSeries", "mk"), Fn("n", Nat(), Normalized(V("n"), App(V("L"), V("n")))));
    private static Formula SourceBody() => App(Q("PowerSeries", "mk"), Fn("i", Nat(),
        Seq(V("if"), Sp, Eqn(V("i"), D(0)), Sp, V("then"), Sp, D(1), Sp, V("else"), Sp,
            Normalized(V("i"), App(Q("MvPolynomial", "X"), V("i"))))));
    private static Formula FamilyBody() => And(Eqn(App(V("L"), D(0)), D(0)),
        Eqn(App(Q("PowerSeries", "logOf"), V("sourceSeries")), SeriesOfFamily()));
    private static Formula ClaimBody() => And(
        ExistsAt("L", FamilyType(), Call("IsSourceFamily", V("L"))),
        All("L", FamilyType(), Imp(Call("IsSourceFamily", V("L")),
            All("n", Nat(), Imp(Le(D(1), V("n")), Eqn(Call("R", V("n"), D(1)), App(V("L"), V("n"))))))));
    private static Formula RecursionBody()
    {
        var m = V("m");
        var k = V("k");
        var r = Call("val", V("r"));
        var term = Mul(Mul(App(Q("MvPolynomial", "C"), Cast(App(Q("Nat", "choose"), m, r), Rat())),
            Call("R", Add(r, D(1)), k)), Call("R", Add(Sub(m, r), D(1)), D(1)));
        var sum = Seq(new Formula.Subscript(Sum, Seq(V("r"), Colon, Sp, Call("Fin", Add(m, D(1))))), Parenthesized(term));
        return new Formula.Aligned([
            All("k", Nat(), Eqn(Call("R", D(0), k), D(0))),
            All("k", Nat(), Eqn(Call("R", D(1), k), App(Q("MvPolynomial", "X"), k))),
            All("m", Nat(), All("k", Nat(), Eqn(Call("R", Add(m, D(2)), k),
                Sub(Call("R", Add(m, D(1)), Add(k, D(1))), sum)))),
        ]);
    }
}
