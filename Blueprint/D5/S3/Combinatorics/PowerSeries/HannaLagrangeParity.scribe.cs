using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PowerSeries;

internal sealed class HannaLagrangeParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PowerSeries/HannaLagrangeParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2023a365574");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangular inversion determines Hanna's integral series and dyadic odd support.",
        H("Hanna's Lagrange parity conjecture for A365574"),
        Blocks(
            Paragraph(Text("PowerSeries has rational coefficients, X is its variable, C embeds a rational "
                + "constant and coeff extracts a coefficient. The superscript -1 denotes the formal "
                + "multiplicative inverse. Subtraction in natural exponents and indices is truncated "
                + "natural subtraction; the restriction n > 1 makes both subtractions exact.")),
            Node("IsGF", "The normalized generating function", GfFormula(),
                "OEIS A365574, NAME (unpaginated): \"Expansion of g.f. A(x) satisfying [x^(n-1)] "
                + "(1 + (n+1)*x*A(x))^n / A(x)^n = n*(n+2)^(n-2) for n > 1.\" "
                + "The offset is zero and a(0) = 1. A is a rational formal power series; "
                + "multiplication by the formal inverse expresses the displayed quotient.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 1", Disp(Equal(V("claim"), Parenthesized(ClaimBody()))),
                "OEIS A365574, COMMENTS (unpaginated): \"Conjecture 1: a(k) is odd iff "
                + "k = 2^n - 2 for n >= 1.\" The proposition asserts existence of a normalized "
                + "solution and integrality with the stated odd support for every normalized solution. "
                + "The exponent n = 1 includes k = 0; the integer m represents the rational coefficient.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The dyadic odd support", Disp(ClaimBody()),
                "The integral series R = X(1-2X^2-2X^3)/((1-X)^2(1+2X)^2) has a compositional "
                + "inverse H with linear coefficient one. Put A = H/X. Partial fractions after a "
                + "Mobius substitution and Lagrange inversion give the diagonal identity. Strong "
                + "induction on inverse coefficients proves uniqueness. Reduction modulo two gives "
                + "H = X(1+H^2), whose coefficients are supported exactly at 2^n-1 for n >= 1.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Series() => Call("PowerSeries", Rationals());
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula IffFormula(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Iff, Sp, Parenthesized(b));
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);

    private static Formula GfFormula() => Disp(All("A", Series(), Equal(Call("IsGF", V("A")),
        Parenthesized(And(Equal(Call("constantCoeff", V("A")), D(1)),
            All("n", Naturals(), Imp(Seq(D(1), Sp, Lt, Sp, V("n")),
                Equal(Call("coeff", Subtract(V("n"), D(1)),
                    Mul(Power(Add(D(1), Mul(Mul(Call("C", Add(Cast(V("n"), Rationals()), D(1))),
                        V("X")), V("A"))), V("n")),
                        Power(Power(V("A"), V("n")), Seq(Minus, D(1))))),
                    Mul(Cast(V("n"), Rationals()), Power(Add(Cast(V("n"), Rationals()), D(2)),
                        Subtract(V("n"), D(2))))))))))));

    private static Formula ClaimBody() => And(
        Some("A", Series(), Call("IsGF", V("A"))),
        All("A", Series(), Imp(Call("IsGF", V("A")), All("k", Naturals(),
            Some("m", Integers(), And(
                Equal(Call("coeff", V("k"), V("A")), Cast(V("m"), Rationals())),
                IffFormula(Call("Odd", V("m")), Some("n", Naturals(),
                    And(Le(D(1), V("n")), Equal(V("k"), Subtract(Power(D(2), V("n")), D(2))))))))))));
}
