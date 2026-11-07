using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PowerSeries;

// generality: I
internal sealed class BalaA337389DiagonalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PowerSeries/BalaA337389Diagonal.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/bala2022a337389");
    private const string SourceName = "Square array T(n,k), n >= 0, k >= 0, read by antidiagonals, where column k is the expansion of sqrt((1+(k-4)*x+sqrt(1-2*(k+4)*x+((k-4)*x)^2)) / (2 * (1-2*(k+4)*x+((k-4)*x)^2))).";
    private const string SourceFormula = "Conjecture: the k-th column entries, k >= 0, are given by [x^n] ( (1 + (k-2)*x + x^2)*(1 + x)^2/(1 - x)^2 )^n. This is true for k = 0 and k = 4. - _Peter Bala_, May 03 2022";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized reversion proves Bala's all-column diagonal formula for A337389.",
        H("Bala's diagonal formula for Manyama's A337389 array"),
        Blocks(
            Paragraph(Text("PowerSeries has rational coefficients; X is its variable, C embeds a "
                + "rational constant, constantCoeff is the constant coefficient, and coeff extracts "
                + "a coefficient. The superscript -1 is the formal multiplicative inverse. Both "
                + "square roots are specified by their equations and constant coefficient one.")),
            Node("delta", "The inner polynomial", DeltaFormula(),
                "OEIS A337389, NAME (unpaginated): " + SourceName
                + " The polynomial delta k is the expression under the inner square root, "
                + "with the natural parameter k cast to the rational field.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsColumn", "The normalized source column", ColumnFormula(),
                "OEIS A337389, NAME (unpaginated): " + SourceName
                + " The series d is the inner root and A is the outer root. Both have constant "
                + "coefficient one; multiplication by the formal inverse expresses the quotient. "
                + "The entries T(n,k) are coeff n A; the array is read by antidiagonals.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("phi", "The diagonal factor", PhiFormula(),
                "OEIS A337389, final FORMULA (unpaginated): " + SourceFormula
                + " The denominator (1-X)^2 is a unit and the expansion is at zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The all-column conjecture", Disp(Equal(V("claim"), Parenthesized(ClaimBody()))),
                "OEIS A337389, final FORMULA (unpaginated): " + SourceFormula
                + " The natural indices include n=0 and every k>=0. Existence of the normalized "
                + "pair is included, and the identity is asserted for every normalized pair.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The all-column diagonal identity", Disp(ClaimBody()),
                "Invert X/phi k compositionally to obtain w=X*phi k(w), and put "
                + "v=(phi k)^(-1)(w), Y=X*w+v and A=PowerSeries.derivative w*v. "
                + "Eliminating w gives Y^2+(C(k)*X-1)*Y+2*(C(k)-2)*X^2+2*X=0. "
                + "Its discriminant gives d=2*Y+C(k)*X-1 with d^2=delta k. Differentiating "
                + "the quadratic and cancelling the units Y-2X and Y+2X gives the outer "
                + "square equation. Lagrange inversion gives coeff n A=coeff n ((phi k)^n). "
                + "Normalized square-root uniqueness identifies every source pair with this pair. "
                + "The argument includes k=0 and k=4 without dividing by k or k-4.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source), new OpenProblemResolutionClaim(ProblemSlugRef.Create("bala337389"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("bala337389-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);
    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Series() => Call("PowerSeries", Rationals());
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Inverse(Formula a) => Power(a, Seq(Minus, D(1)));
    private static Formula Cast(Formula a) => Parenthesized(Seq(a, Colon, Sp, Rationals()));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula ColumnBody() => And(Equal(Call("constantCoeff", V("d")), D(1)),
        And(Equal(Power(V("d"), D(2)), Call("delta", V("k"))),
            And(Equal(Call("constantCoeff", V("A")), D(1)),
                Equal(Power(V("A"), D(2)), Mul(
                    Add(Add(D(1), Mul(Call("C", Subtract(Cast(V("k")), D(4))), V("X"))), V("d")),
                    Inverse(Mul(D(2), Call("delta", V("k")))))))));
    private static Formula DeltaFormula() => Disp(All("k", Naturals(), Equal(Call("delta", V("k")),
        Add(Subtract(D(1), Mul(Call("C", Mul(D(2), Add(Cast(V("k")), D(4)))), V("X"))),
            Power(Mul(Call("C", Subtract(Cast(V("k")), D(4))), V("X")), D(2))))));
    private static Formula ColumnFormula() => Disp(All("k", Naturals(), All("d", Series(), All("A", Series(),
        Equal(Call("IsColumn", V("k"), V("d"), V("A")), Parenthesized(ColumnBody()))))));
    private static Formula PhiFormula() => Disp(All("k", Naturals(), Equal(Call("phi", V("k")),
        Mul(Mul(Add(Add(D(1), Mul(Call("C", Subtract(Cast(V("k")), D(2))), V("X"))),
            Power(V("X"), D(2))), Power(Add(D(1), V("X")), D(2))),
            Inverse(Power(Subtract(D(1), V("X")), D(2)))))));
    private static Formula ClaimBody() => All("k", Naturals(), And(
        Some("d", Series(), Some("A", Series(), Call("IsColumn", V("k"), V("d"), V("A")))),
        All("d", Series(), All("A", Series(), Imp(Call("IsColumn", V("k"), V("d"), V("A")),
            All("n", Naturals(), Equal(Call("coeff", V("n"), V("A")),
                Call("coeff", V("n"), Power(Call("phi", V("k")), V("n"))))))))));
}
