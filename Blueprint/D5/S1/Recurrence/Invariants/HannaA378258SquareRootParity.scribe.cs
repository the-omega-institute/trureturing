using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaA378258SquareRootParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaA378258SquareRootParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2024a378258");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized solution of Hanna's system has integer coefficients, odd exactly at powers of two.",
        H("Integral Compositional Square Roots and Hanna's Parity Conjecture"),
        Blocks(
            Paragraph(Text("PowerSeries is the ring of formal power series and X is its indeterminate. "
                + "The expression PowerSeries.subst(u,f) means f(u(X)); the inner series is the first argument. "
                + "The coefficient operator coeff(n,A) extracts the coefficient of X to the power n. "
                + "The integer m is cast to the rationals when compared with a rational coefficient.")),
            Node("IsGF", "The normalized generating equations", Disp(All("A", Series(),
                Equal(Call("IsGF", F.Id("A")), Parenthesized(GfBody(F.Id("A")))))),
                "The unpaginated OEIS A378258 Name states: \"G.f. satisfies A(x) = B(x) + 5*A(x)^2 "
                + "where B(A(x) - A(x)^2) = x.\" The offset is one and a(1)=1. "
                + "A and B have rational coefficients; the constant coefficient of A is zero and its linear coefficient is one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The parity assertion", Disp(Equal(F.Id("claim"), Parenthesized(ClaimBody()))),
                "The unpaginated OEIS A378258 Comments state: \"Conjecture: a(n) is odd iff n is a power of 2.\" "
                + "A normalized solution exists. For every normalized solution and every natural n at least one, "
                + "its degree-n coefficient is an integer m, and Odd(m) holds exactly when n equals two to a natural power.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Integrality and dyadic parity", Disp(ClaimBody()),
                "Write K for CatalanCompositionSquareParity.catalanSeries, which satisfies K=X+K squared. "
                + "For any integer series H divisible by X squared, successive coefficient corrections "
                + "construct a normalized integer series B with B(B(X))=X+4H and B congruent to X modulo two. "
                + "Each correction is even because the residual is divisible by four, and each corrected degree "
                + "leaves the preceding coefficients unchanged. Apply this construction to H=X-K. "
                + "Composing K with the compositional inverse of B gives an integral solution A of the two equations. "
                + "Uniqueness of normalized compositional square roots over the rationals identifies every rational solution with A. "
                + "Reducing A(B(X))=K modulo two gives A=K modulo two. The coefficient support of K modulo two "
                + "is exactly the powers of two.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("hanna-a378258-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Series() => Call("PowerSeries", Rationals());
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Subst(Formula inner, Formula outer) =>
        new Formula.Apply(Seq(Named("PowerSeries"), Dot, Named("subst")), [inner, outer]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Arrow(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Implies, Sp, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Pow(Formula value, Formula power) => new Formula.Power(value, power);
    private static Formula GfBody(Formula a)
    {
        var b = F.Id("B");
        var square = Pow(a, D(2));
        return And(Equal(Call("constantCoeff", a), D(0)),
            And(Equal(Call("coeff", D(1), a), D(1)),
                Some("B", Series(), And(Equal(a, Add(b, Mul(D(5), square))),
                    Equal(Subst(Sub(a, square), b), F.Id("X"))))));
    }
    private static Formula ClaimBody()
    {
        var a = F.Id("A"); var n = F.Id("n"); var m = F.Id("m");
        return And(Some("A", Series(), Call("IsGF", a)),
            All("A", Series(), Arrow(Call("IsGF", a), All("n", Naturals(),
                Arrow(Seq(D(1), Sp, Le, Sp, n), Some("m", Integers(),
                    And(Equal(Call("coeff", n, a), Parenthesized(Seq(m, Colon, Sp, Rationals()))),
                        Seq(Parenthesized(Call("Odd", m)), Sp, Iff, Sp,
                            Parenthesized(Some("k", Naturals(), Equal(n, Pow(D(2), F.Id("k")))))))))))));
    }
}
