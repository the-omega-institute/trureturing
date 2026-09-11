using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class CubicOddBisectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/CubicOddBisection.";
    private static readonly LibraryNoteRef SourceA =
        LibraryNoteRef.Create("D5/L/Recurrence/manyama2024a372018");
    private static readonly LibraryNoteRef SourceB =
        LibraryNoteRef.Create("D5/L/Recurrence/manyama2024a371364");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd coefficients of A372018 are twice the coefficients of A371364.",
        H("Cubic Odd Bisection"),
        Blocks(
            Paragraph(Text("All series have rational coefficients and indeterminate X. "
                + "The operator coeff(n,f) extracts coefficient n; constantCoeff(f) is coefficient zero. "
                + "The original A372018 formula has a missing argument in A371364(); "
                + "the statement here uses the approved correction A371364(n). "
                + "The two OEIS entries attest the equations and the conjecture. "
                + "The proof below comes from polynomial elimination.")),
            Paragraph(Text("For a polynomial p over the series ring, fixedSeries(c,p) is constructed "
                + "by f(0)=c, f(k+1)=c+X*p(f(k)), taking coefficient n from f(n+1). "
                + "Polynomial differences are divisible by differences of their arguments, "
                + "so each iteration preserves one more coefficient. Thus the resulting series "
                + "satisfies f=c+X*p(f). Here pA(Y)=3Y-Y^2+3XY^2+2X^2Y^3 and "
                + "pB(Y)=8Y^2-3Y-16XY^3; Y is the polynomial variable, independent of X.")),
            Node("A", "The cubic branch", Disp(EqF(A(), Add(D(1),
                Mul(Mul(D(2), X()), Call("fixedSeries", D(1), F.Id("pA")))))),
                "This definition uses only the cubic equation after the substitution A=1+2XH.",
                DescribeRole.Definition),
            Node("B", "The normalized reversion", Disp(EqF(B(),
                Call("fixedSeries", D(1), F.Id("pB")))),
                "This independent iteration rewrites B(1-4XB)^2=1-3XB as "
                + "B=1+X*(8B^2-3B-16XB^3).", DescribeRole.Definition),
            Node("A_equation", "The cubic equation", Disp(AndF(
                EqF(Call("constantCoeff", A()), D(1)), Cubic(A()))),
                "The fixed point for H gives the original cubic after multiplication by -4X; "
                + "the constant coefficient of A is one."),
            Node("B_equation", "The reversion equation", Disp(AndF(
                EqF(Call("constantCoeff", B()), D(1)), Reversion(B()))),
                "Expanding the independent fixed-point equation gives the normalized reversion "
                + "equation. Taking its constant coefficient gives one."),
            Node("A_unique", "Uniqueness of the cubic branch", Disp(Seq(Bound("f", Series()),
                ImpliesF(EqF(Call("constantCoeff", F.Id("f")), D(1)),
                    ImpliesF(Cubic(F.Id("f")), EqF(F.Id("f"), A()))))),
                "Subtract two cubic equations. Their difference is f-A times a factor "
                + "whose constant coefficient is -2, so the factor is nonzero and f=A."),
            Node("B_unique", "Uniqueness of the reversion series", Disp(Seq(Bound("g", Series()),
                ImpliesF(Reversion(F.Id("g")), EqF(F.Id("g"), B())))),
                "The difference of the reversion equations is g-B times a factor with "
                + "constant coefficient one. Cancellation proves uniqueness without "
                + "an additional normalization hypothesis."),
            Node("odd_coeff_identity", "The odd coefficient identity", Disp(Seq(Bound("n", Naturals()),
                OddIdentity(A(), B()))),
                "Put u=A(X), v=-A(-X), and s=u+v. Both u and v satisfy the cubic, "
                + "and u-v has constant coefficient two. Subtraction and cancellation give "
                + "X*(u^2+uv+v^2)-s+3X=0. Subtracting u times this equation from the "
                + "cubic for u gives uv*(1-Xs)+1=0. Elimination now gives "
                + "s*(1-Xs)^2=4X-3X^2*s. The series 4X*B(X^2) satisfies the same equation. "
                + "Its difference from s factors through a series of constant coefficient one, "
                + "so s=4X*B(X^2). Coefficient 2n+1 on the left is twice that of A; "
                + "on the right it is four times coefficient n of B. Dividing by two "
                + "proves the identity for every natural n."),
            Node("odd_coeff_identity_of_equations", "The identity for arbitrary equation witnesses",
                Disp(Seq(Bound("f", Series()), Bound("g", Series()),
                    ImpliesF(EqF(Call("constantCoeff", F.Id("f")), D(1)),
                        ImpliesF(Cubic(F.Id("f")), ImpliesF(Reversion(F.Id("g")),
                            Seq(Bound("n", Naturals()), OddIdentity(F.Id("f"), F.Id("g")))))))),
                "Uniqueness identifies any two witnesses of the original equations with "
                + "the independently constructed A and B, so their coefficients satisfy "
                + "the same identity."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("a372018-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(SourceA, SourceB), Blocks(Paragraph(Text(prose))), role);

    private static Formula A() => F.Id("A");
    private static Formula B() => F.Id("B");
    private static Formula X() => F.Id("X");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Series() => Call("PowerSeries", Seq(Mathbb, Grp(F.Id("Q"))));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula EqF(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, byte k) => new Formula.Power(a, D(k));
    private static Formula AndF(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula ImpliesF(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Cubic(Formula f) => EqF(
        Add(Add(Sub(Mul(X(), Pow(f, 3)), Pow(f, 2)), Mul(Mul(D(3), X()), f)), D(1)), D(0));
    private static Formula Reversion(Formula f) => EqF(
        Mul(f, Pow(Par(Sub(D(1), Mul(Mul(D(4), X()), f))), 2)),
        Sub(D(1), Mul(Mul(D(3), X()), f)));
    private static Formula OddIdentity(Formula f, Formula g) => EqF(
        Call("coeff", Add(Mul(D(2), F.Id("n")), D(1)), f),
        Mul(D(2), Call("coeff", F.Id("n"), g)));
}
