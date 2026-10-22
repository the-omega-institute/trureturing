using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.HannaBilateral;

internal sealed class OeisA363558PowerOfTwoDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2023bilateral");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's A363558 power-of-two coefficient formula.",
        H("Hanna's A363558 Power-of-Two Formula"),
        Blocks(
            Node("coeffA", "The bilateral coefficients", CoeffDefinition(), "Expansion of g.f. A(x) = Sum_{n=-oo..+oo} x^n * (2 + x^n)^(2*n). The parameter c is complex, m is a natural degree, and coeff extracts a formal power-series coefficient. The nonnegative summands are polynomials. The summand indexed by the negative integer -k is expressed as X^(2*k^2-k) times the inverse of (1+C(c)*X^k)^(2*k). Both degree-m sums are finite; no analytic convergence is asserted.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "The A363558 sequence", Disp(All("m", Nat(), Eqn(Call("a", X("m")), Call("coeffA", D(2), X("m"))))), "Expansion of g.f. A(x) = Sum_{n=-oo..+oo} x^n * (2 + x^n)^(2*n). The parameter is 2.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Hanna's A363558 conjecture", Disp(Eqn(X("claim"), Parenthesized(ClaimBody()))), "a(2^n) = 4^(2^n) for n > 0 (conjecture). Source: OEIS A363558, FORMULA field (an unpaginated entry). Indices are natural numbers; values and numeric expressions on both sides are complex. The displayed hypotheses retain the source range.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("coeffA_prime", "Prime-index coefficients for every complex parameter", Disp(All("c", Cplx(), All("p", Nat(), Imp(App(Q("Nat", "Prime"), X("p")), Imp(Lt(D(3), X("p")), Eqn(Call("coeffA", X("c"), X("p")), Add(Mul(Cast(X("p"), Cplx()), Pow(X("c"), Sub(X("p"), D(1)))), Pow(X("c"), Mul(D(2), X("p")))))))))), "For a prime greater than three, the divisor sums have only the two endpoint divisors. The smaller positive contribution vanishes, and the negative contribution has even exponent. This identity gives the four prime-index sequence formulas.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("coeffA_pow_two", "Dyadic coefficients for every complex parameter", Disp(All("c", Cplx(), All("N", Nat(), Imp(Lt(D(0), X("N")), Eqn(Call("coeffA", X("c"), Pow(D(2), X("N"))), Pow(X("c"), Pow(D(2), Add(X("N"), D(1))))))))), "For a positive dyadic exponent, pair the positive term at divisor 2^i with the negative term at divisor 2^(N-1-i). Their binomial coefficients agree and their signs are opposite. The largest positive divisor contributes the remaining power. The four dyadic sequence formulas are instances of this identity.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "The A363558 power-of-two formula", Disp(ClaimBody()), "Apply the complex-parameter dyadic coefficient identity and simplify the indicated parameter powers.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula ClaimBody() => All("n", Nat(), Imp(Lt(D(0), X("n")), Eqn(Call("a", Pow(D(2), X("n"))), Pow(D(4), Pow(D(2), X("n"))))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hanna-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role,
            name == "result"
                ? new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a363558-a363569-hanna-bilateral-power-and-prime-values"), ResolutionKind.Proved)
                : null);
    private static Formula X(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Cplx() => Seq(Mathbb, Grp(X("C")));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, X(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);

    private static Formula CoeffDefinition() => Disp(All("c", Cplx(), All("m", Nat(),
        Eqn(Call("coeffA", X("c"), X("m")), Add(
            SumOver("n", App(Q("Finset", "range"), Add(X("m"), D(1))),
                App(Q("PowerSeries", "coeff"), X("m"),
                    Mul(Pow(Cast(Q("PowerSeries", "X"), Call("PowerSeries", Cplx())), X("n")),
                        Pow(Add(App(Q("PowerSeries", "C"), X("c")), Pow(Q("PowerSeries", "X"), X("n"))), Mul(D(2), X("n")))))),
            SumOver("k", App(Q("Finset", "Icc"), D(1), X("m")),
                App(Q("PowerSeries", "coeff"), X("m"),
                    Mul(Pow(Cast(Q("PowerSeries", "X"), Call("PowerSeries", Cplx())), Sub(Mul(D(2), Pow(X("k"), D(2))), X("k"))),
                        Pow(Pow(Add(D(1), Mul(App(Q("PowerSeries", "C"), X("c")), Pow(Q("PowerSeries", "X"), X("k")))), Mul(D(2), X("k"))), Seq(Minus, D(1)))))))))));
    private static Formula SumOver(string name, Formula set, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(X(name), Sp, InMacro, Sp, set)), Sp, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
