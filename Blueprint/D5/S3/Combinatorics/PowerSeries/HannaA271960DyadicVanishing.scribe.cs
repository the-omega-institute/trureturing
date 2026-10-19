using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PowerSeries;

internal sealed class HannaA271960DyadicVanishingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PowerSeries/HannaA271960DyadicVanishing.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2016a271960");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reversion and dyadic coefficient decimation prove Hanna's A271960 conjecture.",
        H("Hanna's dyadic vanishing conjecture for A271960"),
        Blocks(
            Paragraph(Text("All series have rational coefficients. The operation subst(u,f) "
                + "is PowerSeries.subst u f, namely f(u). Natural subtraction in the coefficient "
                + "index is exact under the displayed bounds.")),
            Node("IsGF", "The normalized generating function", GfFormula(),
                "OEIS A271960, NAME (unpaginated): \"G.f. A(x) satisfies: A(x)^2 = A( (x + 2*A(x)^2)^2 ).\" "
                + "OFFSET 1 and EXAMPLE A(x) = x + 2*x^2 + 9*x^3 + 50*x^4 + 312*x^5 + … "
                + "specify zero constant coefficient and linear coefficient one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("xOverA", "The quotient x divided by A(x)", QuotientFormula(),
                "Deleting the zero constant coefficient from A gives A(x)/x. Its multiplicative "
                + "inverse is x/A(x); the linear coefficient of A makes this series a unit.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The OEIS conjecture", Disp(Equal(V("claim"), Parenthesized(ClaimBody()))),
                "OEIS A271960, COMMENTS (unpaginated): \"Conjecture: [x^(2^n-2^k)] (x/A(x))^(2^n) = 0 "
                + "for k = 0..n-2 and n >= 2. - _Paul D. Hanna_, Jan 16 2026\" "
                + "Here n and k are natural numbers, coeff extracts a coefficient, and IsGF "
                + "also specifies the normalization. The proposition includes existence of a solution "
                + "and the assertion for every normalized solution.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Dyadic vanishing", Disp(ClaimBody()),
                "Let B be the compositional inverse of A and H=B+2X^2. The defining equation "
                + "implies H^2=B(X^2), and the linear coefficient of H forces H(-X)=-H(X). "
                + "Expanding B^r=(H-2X^2)^r eliminates odd powers at even degrees; the remaining "
                + "terms reduce both degree and exponent by a factor of two. Induction proves "
                + "coeff N (B^r)=0 whenever 2r<N, 2^s divides N-2r and r<2^s. Lagrange "
                + "inversion transfers this to the displayed coefficient with N=2^n and r=2^k. "
                + "Existence follows by coefficientwise stabilization of the iteration "
                + "F ↦ F + (F(X^2)-F^2-2X)/2, starting at one, followed by compositional inversion.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hanna-a271960-dyadic-vanishing"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role, resolution);

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
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula GfFormula() => Disp(All("A", Series(), Seq(
        Call("IsGF", V("A")), Sp, Iff, Sp, Parenthesized(And(
            Equal(Call("constantCoeff", V("A")), D(0)), And(
                Equal(Call("coeff", D(1), V("A")), D(1)),
                Equal(Power(V("A"), D(2)), Call("subst", Power(Add(V("X"),
                    Mul(D(2), Power(V("A"), D(2)))), D(2)), V("A")))))))));
    private static Formula QuotientFormula() => Disp(All("A", Series(), Equal(Call("xOverA", V("A")),
        Power(Call("mk", Parenthesized(Seq(V("n"), Colon, Sp, Naturals(), Sp, Mapsto, Sp,
            Call("coeff", Add(V("n"), D(1)), V("A"))))), Seq(Minus, D(1))))));
    private static Formula ClaimBody() => And(
        Seq(Exists, Sp, V("A"), Colon, Sp, Series(), Comma, Sp, Call("IsGF", V("A"))),
        All("A", Series(), Imp(Call("IsGF", V("A")), All("n", Naturals(), All("k", Naturals(),
            Imp(Le(D(2), V("n")), Imp(Le(V("k"), Subtract(V("n"), D(2))),
                Equal(Call("coeff", Subtract(Power(D(2), V("n")), Power(D(2), V("k"))),
                    Power(Call("xOverA", V("A")), Power(D(2), V("n")))), D(0)))))))));
}
