using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class HannaPrimePowerCorrectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/HannaPrimePowerCorrection.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/hanna2025a384819");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every bounded integral square-weight correction equals p minus one at p to any positive power.",
        H("Hanna's Prime-Power Correction Formula"),
        Blocks(
            Paragraph(Text("The sequence a has integer values and starts at index one; a(0) is unused. "
                + "All power series have rational coefficients, and every exponential and substitution "
                + "is formal. IntegralSeries is the predicate from HannaLogarithmicPowerClosure: "
                + "every ordinary coefficient is the image of an integer. The displayed casts are "
                + "the canonical embeddings into the indicated carrier. Division in the exponent "
                + "is rational field division. PowerSeries.subst takes the substituted series first "
                + "and the series into which it is substituted second. The function ite selects "
                + "its second argument when its first argument holds and its third argument otherwise.")),
            Node("IsCorrection", "The defining integral-series condition", CorrectionFormula(),
                "OEIS A384819, revision 14, NAME (no page number): "
                + "\"Nonnegative numbers a(n) < n for n >= 1 such that exp( Sum_{n>=1} (n^2 - a(n))*x^n/n ) is a power series with integral coefficients.\" "
                + "The natural index m denotes the source index n. The coefficient at m=0 "
                + "of the exponent is zero, and every positive coefficient is (m^2-a(m))/m. "
                + "No sign condition is imposed on the exponential coefficients or Euler exponents.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Hanna's conjecture", Disp(Equal(Call("claim"), Parenthesized(ClaimBody()))),
                "OEIS A384819, revision 14, sole COMMENTS line (no page number): "
                + "\"Conjecture: a(p^n) = p - 1 when p is prime for n >= 1.\" "
                + "The positive source exponent n is renamed r. The assertion holds for every "
                + "integer sequence satisfying the defining condition, every natural prime p, "
                + "including two, and every positive natural r.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "All positive prime powers", Disp(ClaimBody()),
                "An integer Euler ledger gives m^2-a(m) as the sum of d times the ledger "
                + "entry over positive divisors d of m. The difference between the divisor "
                + "sums at successive prime powers is divisible by the larger prime power. "
                + "The bound at one gives a(1)=0; at p it gives the representative p-1. "
                + "For higher powers the square terms vanish modulo the larger prime power, "
                + "and uniqueness of a representative in the bounded interval preserves p-1. "
                + "The integer ledger theorem is integral_input_ledger in "
                + "HannaDiagonalGhostPowerIntegrality. The conclusion is unbounded in p and r.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a384819-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula CorrectionFormula()
    {
        var a = V("a");
        var m = V("m");
        var bounds = All("m", N(), Imp(Leq(D(1), m),
            And(Leq(D(0), App(a, m)), Less(App(a, m), Cast(m, Z())))));
        var coefficient = Call("ite", Equal(m, D(0)), D(0),
            new Formula.Fraction(Sub(Pow(Cast(m, Q()), D(2)), Cast(App(a, m), Q())), Cast(m, Q())));
        var exponent = App(Qualified("PowerSeries", "mk"), Lambda("m", N(), coefficient));
        var series = App(Qualified("PowerSeries", "subst"), exponent,
            App(Qualified("PowerSeries", "exp"), Q()));
        return Disp(All("a", Function(N(), Z()),
            Equal(Call("IsCorrection", a), Parenthesized(And(bounds, Call("IntegralSeries", series))))));
    }

    private static Formula ClaimBody()
    {
        var a = V("a");
        var p = V("p");
        var r = V("r");
        return All("a", Function(N(), Z()), Imp(Call("IsCorrection", a),
            All("p", N(), All("r", N(), Imp(App(Qualified("Nat", "Prime"), p),
                Imp(Leq(D(1), r), Equal(App(a, Pow(p, r)), Sub(Cast(p, Z()), D(1)))))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Function(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
}
