using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class ForbergExponentialFloorDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/SeriesInequalities/ForbergExponentialFloor.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/AnalyticClosure/forberg2013a002620");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Forberg's exponential quotient has the shifted quarter-square floor at every positive integer.",
        H("Forberg Exponential Floor"),
        Blocks(Describe.Lean(
            DescribeId.Create("forberg-exponential-floor-result"),
            DeclarationHandle.Create(Module + "result"),
            H("The whole positive-integer identity"),
            StatementSource.FromAuthor(Identity()),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text("Let n be a natural number with 1 <= n. All subtraction, division, squaring and exponential arguments in the formula are real arithmetic: n is first coerced to the reals, exp means Real.exp, and both floors take values in the integers. In particular, n-1 is real subtraction. The statement includes n=1, both parities and arbitrarily large n.")),
                Paragraph(Text("OEIS A002620 defines the quarter-squares by a(m)=floor(m^2/4). Richard R. Forberg's empirical formula is a(n-1)=floor(n/(exp(4/n)-1)); substituting m=n-1 gives the displayed identity.")),
                Paragraph(Text("For every real r >= 2, the analytic estimate is (r-1)^2/4 <= r/(exp(4/r)-1) < r^2/4-r/2+1. To prove the lower bound, put q=(1+1/r)/(1-1/r). The logarithmic series bound gives 4/r <= 2 log(q), hence exp(4/r) <= ((r+1)/(r-1))^2. The denominator exp(4/r)-1 is positive, so division gives the required lower bound. The upper bound follows from exp(4/r) >= 1+4/r+(4/r)^2/2 and multiplication by positive quantities.")),
                Paragraph(Text("For n=2k, both real expressions lie in the integer floor interval [k(k-1),k(k-1)+1). For n=2k+1, both lie in [k^2,k^2+1). The two-sided estimate supplies these intervals for all n >= 2. At n=1 the quadratic exponential bound gives 0 <= 1/(exp(4)-1) < 1, while the shifted square is zero. The characterization floor(x)=z if and only if z <= x < z+1 finishes every case.")),
                Paragraph(Text("The logarithmic, quadratic exponential, order and floor facts are classical. The identity is stated on the positive integers; no real-parameter extension or claim of priority is asserted."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Floor(Formula a) => Seq(Lfloor, Sp, a, Rfloor);
    private static Formula Identity() => Disp(Seq(
        Forall, Sp, V("n"), Colon, Sp, Mathbb, Grp(V("N")), Comma, Sp,
        D(1), Leq, Sp, V("n"), Sp, Implies, Sp,
        new Formula.Relation(
            Floor(Div(V("n"), Sub(
                new Formula.FunctionCall(FormulaIdentifier.Create("exp"), [Div(D(4), V("n"))]), D(1)))),
            FormulaRelationOperator.Equal,
            Floor(Div(new Formula.Power(Seq(Open, Sub(V("n"), D(1)), Close), D(2)), D(4))))));
}
