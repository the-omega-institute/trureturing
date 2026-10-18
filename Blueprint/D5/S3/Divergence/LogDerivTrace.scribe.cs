using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class LogDerivTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var index = F.Id("iota");
        var matrix = Call("Matrix", index, index, F.Id("C"));
        var m = F.Id("m");
        var x = F.Id("X");

        return DocumentDefinition.Create(ScribeNode.Create(
            "The trace identity for the integral logarithmic directional derivative.",
            H("Logarithmic Derivative Trace Identity"),
            Blocks(
                Published("scalarKernel_integrable", "Scalar inverse-square integrability", ScalarKernel(),
                    "For positive lambda, the function lambda divided by (lambda plus t) squared is integrable on the positive half-line."),
                Published("pairKernel_integrable", "Paired resolvent integrability", PairKernel(),
                    "For positive a and b, the reciprocal of (a plus t) times (b plus t) is integrable on the positive half-line."),
                Published("resolvent_eq_spectral", "The resolvent in the eigenbasis", Spectral(),
                    "The inverse of a positive definite matrix plus t times the identity is obtained by taking reciprocal shifted eigenvalues in its unitary eigenbasis, for nonnegative t."),
                Published("logDeriv_integrable", "Matrix logarithmic derivative integrability", LogIntegral(),
                    "For positive definite m and any complex direction X, the two-resolvent sandwich is Bochner integrable on the positive half-line."),
                                Describe.Lean(
                    DescribeId.Create("integral-logarithmic-directional-derivative"),
                    DeclarationHandle.Create(
                        "D5/S3/Divergence/LogDerivTrace.logDeriv"),
                    H("Integral logarithmic directional derivative"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For a complex square matrix m and direction X, logDeriv m X is " +
                            "the matrix-valued Bochner integral over positive real t of " +
                            "(m + t I)^(-1) X (m + t I)^(-1). The notation D ln in the source " +
                            "paper denotes this integral. The declaration does not assert that " +
                            "logDeriv is the Frechet derivative of Matrix.log; the pinned " +
                            "Mathlib API exposes the matrix logarithm through CFC.log and " +
                            "supplies no theorem identifying that derivative with this integral."))),
                    DescribeRole.Definition),
                                Describe.Lean(
                    DescribeId.Create("positive-definite-log-derivative-has-direction-trace"),
                    DeclarationHandle.Create(
                        "D5/S3/Divergence/LogDerivTrace.trace_mul_logDeriv"),
                    H("Positive definite logarithmic derivative has the direction trace"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("m"),
                        Call("PositiveDefinite", matrix),
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("X"),
                            Call("Hermitian", matrix),
                            Equal(
                                Call("trace", Call("multiply", m, Call("logDeriv", m, x))),
                                Call("trace", x))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let m be positive definite and X Hermitian. Unitary spectral " +
                            "decomposition writes each resolvent in the eigenbasis of m. " +
                            "Entrywise inverse-square majorants prove Bochner integrability, " +
                            "and fixed matrix multiplication and trace commute with the " +
                            "integral by finite-dimensional continuity. Trace cyclicity reduces " +
                            "the integrand to a finite sum whose ith scalar kernel is " +
                            "lambda_i/(lambda_i+t)^2. Every lambda_i is positive and the " +
                            "integral of this kernel over positive t is one, leaving the trace " +
                            "of the unitary conjugate of X, hence the trace of X. The Hermitian " +
                            "hypothesis is retained to state the identity on the paper's " +
                            "declared domain."))),
                    DescribeRole.Theorem))));
    }

    private static DocumentBlock Published(string name, string title, Formula f, string prose) => Describe.Lean(
        DescribeId.Create("log-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create("D5/S3/Divergence/LogDerivTrace." + name),
        H(title), StatementSource.FromAuthor(f), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Lemma);
    private static Formula V(string n) => F.Id(n);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula A(string n, Formula t, Formula b) => Seq(Forall, Sp, Parenthesized(Seq(V(n), Colon, Sp, t)), Comma, Sp, b);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula I => V("iota");
    private static Formula M => Call("Matrix", I, I, C);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Scale(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Inv(Formula a) => Pow(Parenthesized(a), Seq(Minus, Sp, D(1)));
    private static Formula Lam(string n, Formula t, Formula b) => Parenthesized(Seq(Parenthesized(Seq(V(n), Colon, Sp, t)), Sp, Mapsto, Sp, b));
    private static Formula Halfline => Seq(Operatorname, Grp(V("Set")), Dot, Operatorname, Grp(V("Ioi")), Parenthesized(D(0)));
    private static Formula Generic(Formula b) => A("iota", V("Type"), Seq(
        OpenBracket, Call("Fintype", I), CloseBracket, Sp, OpenBracket, Call("DecidableEq", I), CloseBracket, Comma, Sp, b));
    private static Formula ScalarKernel() => Disp(A("lambda", R, Imp(Lt(D(0), V("lambda")),
        Call("IntegrableOn", Lam("t", R, new Formula.Fraction(V("lambda"), Pow(Parenthesized(Add(V("lambda"), V("t"))), D(2)))), Halfline))));
    private static Formula PairKernel() => Disp(A("a", R, A("b", R,
        Imp(Lt(D(0), V("a")), Imp(Lt(D(0), V("b")), Call("IntegrableOn", Lam("t", R,
            new Formula.Fraction(D(1), Mul(Parenthesized(Add(V("a"), V("t"))), Parenthesized(Add(V("b"), V("t")))))), Halfline))))));
    private static Formula Shift => Add(V("m"), Scale(V("t"), D(1)));
    private static Formula LogIntegral() => Disp(Generic(A("m", M, A("X", M, Imp(Call("PosDef", V("m")),
        Call("IntegrableOn", Lam("t", R, Mul(Mul(Inv(Shift), V("X")), Inv(Shift))), Halfline))))));
    private static Formula Field(Formula a, string f) => Seq(a, Dot, Operatorname, Grp(V(f)));
    private static Formula Spectral()
    {
        var hermitian = Field(V("hm"), "isHermitian");
        var unitary = Field(hermitian, "eigenvectorUnitary");
        var eigenvalues = Field(hermitian, "eigenvalues");
        var value = Inv(Parenthesized(Seq(Add(Seq(eigenvalues, Parenthesized(V("i"))), V("t")), Colon, Sp, C)));
        var diagonal = Call("diagonal", Lam("i", I, value));
        return Disp(Generic(A("m", M, A("hm", Call("PosDef", V("m")), A("t", R,
            Imp(Le(D(0), V("t")), Equal(Inv(Shift), Mul(Mul(unitary, diagonal), Call("star", unitary)))))))));
    }
}
