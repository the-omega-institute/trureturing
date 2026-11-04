using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaThueRothExponentialIntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaThueRothExponentialIntegrality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2010a174470");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's Thue/Roth weighted formal exponential has integer coefficients.",
        H("Hanna's Thue/Roth Exponential Integrality"),
        Blocks(
            Node("b", "The Thue/Roth bits",
                All("n", N(), Eqn(Call("b", V("n")), BitBody())),
                "OEIS A014578, NAME field (no page number): “Binary expansion of Thue constant (or Roth's constant).” Its FORMULA field states: “a(0)=0; a(3k)=1-a(k) for k>=1; a(3k+1)=a(3k+2)=1 for k>=0. - _Benoit Cloitre_, Mar 19 2004”. Here b takes values in the integers. The zero term is zero; at a positive n, the value is one exactly when the three-adic valuation is even. Nat.mod is natural-number remainder.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("c", "The logarithmic weights",
                All("n", N(), Eqn(Call("c", V("n")),
                    Mul(Call("b", V("n")), new Formula.Power(Cast(D(3), Z()), V("n"))))),
                "OEIS A174470, NAME field (no page number): “G.F.: exp( Sum_{n>=1} A014578(n)*(3x)^n/n ), where A014578 is the binary expansion of Thue constant.” The weight c(n) is b(n) times 3 to the n-th power.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsSourceSeries", "The specified rational series",
                All("A", PS(), Seq(Call("IsSourceSeries", V("A")), Sp, Iff, Sp,
                    Parenthesized(Eqn(V("A"), SourceSeries())))),
                "OEIS A174470, NAME field (no page number): “G.F.: exp( Sum_{n>=1} A014578(n)*(3x)^n/n ), where A014578 is the binary expansion of Thue constant.” A is a rational formal power series. DoldExponentialIntegrality.logInput c has degree-n coefficient c(n)/n over the rationals and constant coefficient zero. PowerSeries.subst takes this input first and PowerSeries.exp ℚ second; no analytic convergence is required.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Hanna's integrality assertion",
                Seq(V("claim"), Sp, Iff, Sp, Parenthesized(ClaimBody())),
                "OEIS A174470, COMMENT field (no page number): “Conjectured to consist entirely of integers.” The NAME field reads: “G.F.: exp( Sum_{n>=1} A014578(n)*(3x)^n/n ), where A014578 is the binary expansion of Thue constant.” Existence of A is included. Every ordinary coefficient, at every natural degree N including zero, is the rational image of an integer z.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "All coefficients are integers", ClaimBody(),
                "The specified rational series exists and all its coefficients are integers. For the prime 3, the inequality v₃(m)+1 ≤ m makes both weights divisible by the required power of 3. At every other prime p, b(pm)=b(m), and Euler's congruence modulo p raised to vₚ(m)+1 supplies the power difference, including p=2. The Dold exponential-integrality theorem gives the conclusion at every natural degree, including the constant term.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hanna-a174470"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("hannathueroth-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(name))), [.. args]);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula PS() => Call("PowerSeries", Q());
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula BitBody()
    {
        var valuation = Call("padicValNat", D(3), V("n"));
        var even = Eqn(Qualified("Nat", "mod", valuation, D(2)), D(0));
        var positiveCase = Seq(V("if"), Sp, Parenthesized(even), Sp, V("then"), Sp, D(1),
            Sp, V("else"), Sp, D(0));
        return Seq(V("if"), Sp, Parenthesized(Eqn(V("n"), D(0))), Sp, V("then"), Sp, D(0),
            Sp, V("else"), Sp, Parenthesized(positiveCase));
    }
    private static Formula SourceSeries() =>
        Qualified("PowerSeries", "subst",
            Qualified("DoldExponentialIntegrality", "logInput", V("c")),
            Qualified("PowerSeries", "exp", Q()));
    private static Formula ClaimBody()
    {
        var integral = All("N", N(), Ex("z", Z(),
            Eqn(Qualified("PowerSeries", "coeff", V("N"), V("A")), Cast(V("z"), Q()))));
        var allSeries = All("A", PS(), Seq(Parenthesized(Call("IsSourceSeries", V("A"))),
            Sp, Implies, Sp, Parenthesized(integral)));
        return Seq(Parenthesized(Ex("A", PS(), Call("IsSourceSeries", V("A")))),
            Sp, Land, Sp, Parenthesized(allSeries));
    }
}
