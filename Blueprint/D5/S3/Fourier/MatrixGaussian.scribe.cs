using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class MatrixGaussianDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every finite coordinate type n, real positive definite A, complex b with positive real part and real frequency w, the integral of exp(-2 pi i w dot x) exp(-pi b Q_A(x)) is sqrt(det A)^(-1) b^(-card(n)/2) exp(-pi Q_(A^(-1))(w)/b). The right half-plane excludes the inverse-power branch cut.",
        H("MatrixGaussian"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("matrixgaussian-quadratic"),
                DeclarationHandle.Create("D5/S3/Fourier/MatrixGaussian.quadratic"),
                H("Coordinate quadratic form"),
                StatementSource.FromAuthor(QuadraticFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite coordinate set n and real square matrix A, quadratic A x is x dotProduct (A mulVec x), with both operations in real coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("matrixgaussian-integrable-gaussian-linear"),
                DeclarationHandle.Create("D5/S3/Fourier/MatrixGaussian.integrable_gaussian_linear"),
                H("Integrability with complex linear phase"),
                StatementSource.FromAuthor(IntegrableFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite coordinate type n, real positive definite A, complex b with positive real part, complex c and real coordinate vector w, exp(-b Q_A(x)+c w dot x) is integrable for coordinate Lebesgue measure. The empty coordinate set is included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matrixgaussian-integral-gaussian-linear"),
                DeclarationHandle.Create("D5/S3/Fourier/MatrixGaussian.integral_gaussian_linear"),
                H("The coordinate Gaussian integral"),
                StatementSource.FromAuthor(IntegralFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite coordinate type n, real positive definite A, complex b with positive real part, complex c and real w, the coordinate Lebesgue integral of exp(-b Q_A(x)+c w dot x) is sqrt(det A)^(-1) (pi/b)^(card(n)/2) exp(c^2 Q_(A^(-1))(w)/(4b)). Complex powers use the principal branch. The change of variables is the real positive matrix square root; its determinant gives the coordinate-volume factor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matrixgaussian-integral-fourier-gaussian"),
                DeclarationHandle.Create("D5/S3/Fourier/MatrixGaussian.integral_fourier_gaussian"),
                H("The normalized matrix Fourier kernel"),
                StatementSource.FromAuthor(FourierFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite coordinate type n, real positive definite A, complex b with positive real part and real frequency w, the integral of exp(-2 pi i w dot x) exp(-pi b Q_A(x)) is sqrt(det A)^(-1) b^(-card(n)/2) exp(-pi Q_(A^(-1))(w)/b). The right half-plane excludes the inverse-power branch cut."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Imag => Seq(Operatorname, Grp(V("Complex")), Dot, Operatorname, Grp(V("I")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Pos(Formula a) => new Formula.Relation(D(0), FormulaRelationOperator.LessThan, a);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula NegF(Formula a) => new Formula.Negate(a);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Inv(Formula a) => Pow(a, NegF(D(1)));
    private static Formula Cast(Formula a, Formula t) => Seq(Open, a, Colon, t, Close);
    private static Formula Lam(string s, Formula t, Formula p) => Seq(Open, V(s), Colon, t, Sp, Mapsto, Sp, p, Close);
    private static Formula ExpF(Formula x) => Call("exp", x);
    private static Formula Mat(Formula n, Formula t) => Call("Matrix", n, n, t);
    private static Formula Q(Formula a, Formula x) => Call("quadratic", a, x);
    private static Formula Integral(string s, Formula t, Formula p) => Call("integral", Lam(s, t, p), Call("volume", t));
    private static Formula G(Formula a, Formula b, Formula x) => ExpF(Mul(Mul(NegF(Pi), b), Cast(Q(a, x), C)));
    private static Formula DualG(Formula a, Formula b, Formula x) => ExpF(Mul(Div(NegF(Pi), b), Cast(Q(Inv(a), x), C)));
    private static Formula Inst(string cls, Formula n) => Seq(OpenBracket, Call(cls, n), CloseBracket, Sp);
    private static Formula FiniteType(Formula p) => All("n", V("Type"), Seq(Inst("Fintype", V("n")), Inst("DecidableEq", V("n")), p));
    private static Formula PositiveMatrix(Formula n, Formula p) => All("A", Mat(n, R), Imp(Call("PosDef", V("A")), p));
    private static Formula RightParameter(Formula p) => All("b", C, Imp(Pos(Call("re", V("b"))), p));
    private static Formula DetFactor(Formula a) => Inv(Cast(Call("sqrt", Call("det", a)), C));

    private static Formula LinearTerm(Formula n) => ExpF(Add(
        Mul(NegF(V("b")), Cast(Q(V("A"), V("x")), C)),
        Mul(V("c"), Cast(Call("dotProduct", V("w"), V("x")), C))));
    private static Formula GaussianParameters(Formula p) => FiniteType(PositiveMatrix(V("n"),
        RightParameter(All("c", C, All("w", Arr(V("n"), R), p)))));
    private static Formula QuadraticFormula() => Disp(FiniteType(All("A", Mat(V("n"), R),
        All("x", Arr(V("n"), R), Equal(Q(V("A"), V("x")),
            Call("dotProduct", V("x"), Call("mulVec", V("A"), V("x"))))))));
    private static Formula IntegrableFormula() => Disp(GaussianParameters(Call("Integrable",
        Lam("x", Arr(V("n"), R), LinearTerm(V("n"))), Call("volume", Arr(V("n"), R)))));
    private static Formula IntegralFormula() => Disp(GaussianParameters(Equal(
        Integral("x", Arr(V("n"), R), LinearTerm(V("n"))),
        Mul(Mul(DetFactor(V("A")), Pow(Div(Pi, V("b")), Div(Cast(Call("card", V("n")), C), D(2)))),
            ExpF(Div(Mul(Pow(V("c"), D(2)), Cast(Q(Inv(V("A")), V("w")), C)), Mul(D(4), V("b"))))))));
    private static Formula FourierFormula()
    {
        Formula phase = ExpF(Mul(Mul(Mul(NegF(D(2)), Pi), Imag),
            Cast(Call("dotProduct", V("w"), V("x")), C)));
        Formula rhs = Mul(Mul(DetFactor(V("A")),
            Pow(V("b"), Div(NegF(Cast(Call("card", V("n")), C)), D(2)))),
            DualG(V("A"), V("b"), V("w")));
        return Disp(FiniteType(PositiveMatrix(V("n"), RightParameter(All("w", Arr(V("n"), R),
            Equal(Integral("x", Arr(V("n"), R), Mul(phase, G(V("A"), V("b"), V("x")))), rhs))))));
    }
}
