using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class MatrixGaussianThetaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every natural rank r, real positive definite A and complex tau with positive imaginary part, theta A (-1/tau) equals (-i tau)^(r/2) divided by sqrt(det A), times theta (A^(-1)) tau. The power is principal and rank zero is included.",
        H("MatrixGaussianTheta"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("matrixgaussiantheta-theta"),
                DeclarationHandle.Create("D5/S3/Fourier/MatrixGaussianTheta.theta"),
                H("Real matrix theta series"),
                StatementSource.FromAuthor(ThetaFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each natural rank r, real coordinate matrix A and complex tau, theta A tau is the sum over all integer vectors a of exp(pi i tau Q_A(a))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("matrixgaussiantheta-summable-norm-theta"),
                DeclarationHandle.Create("D5/S3/Fourier/MatrixGaussianTheta.summable_norm_theta"),
                H("Upper half-plane norm convergence"),
                StatementSource.FromAuthor(SummableFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural rank r, real positive definite A and complex tau with positive imaginary part, the norms of the terms defining theta A tau are summable."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matrixgaussiantheta-theta-inversion"),
                DeclarationHandle.Create("D5/S3/Fourier/MatrixGaussianTheta.theta_inversion"),
                H("Inverse-matrix theta inversion"),
                StatementSource.FromAuthor(InversionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural rank r, real positive definite A and complex tau with positive imaginary part, theta A (-1/tau) equals (-i tau)^(r/2) divided by sqrt(det A), times theta (A^(-1)) tau. The power is principal and rank zero is included."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Imag => Seq(Operatorname, Grp(V("Complex")), Dot, Operatorname, Grp(V("I")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Z => Seq(Mathbb, Grp(V("Z")));
    private static Formula N => Seq(Mathbb, Grp(V("N")));
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
    private static Formula At(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula ExpF(Formula x) => Call("exp", x);
    private static Formula FinR => Call("Fin", V("r"));
    private static Formula Mat(Formula n, Formula t) => Call("Matrix", n, n, t);
    private static Formula Q(Formula a, Formula x) => Call("quadratic", a, x);
    private static Formula IntVec(Formula n, Formula a) => Lam("i", n, Cast(At(a, V("i")), R));
    private static Formula Tsum(string s, Formula t, Formula p) => Call("tsum", Lam(s, t, p));
    private static Formula Summable(string s, Formula t, Formula p) => Call("Summable", Lam(s, t, p));
    private static Formula PositiveMatrix(Formula n, Formula p) => All("A", Mat(n, R), Imp(Call("PosDef", V("A")), p));
    private static Formula UpperParameter(Formula p) => All("tau", C, Imp(Pos(Call("im", V("tau"))), p));
    private static Formula RankMatrix(Formula p) => All("r", N, PositiveMatrix(FinR, p));
    private static Formula ThetaTerm(Formula a, Formula x) => ExpF(Mul(Mul(Mul(Pi, Imag), V("tau")), Cast(Q(a, x), C)));
    private static Formula DetFactor(Formula a) => Inv(Cast(Call("sqrt", Call("det", a)), C));

    private static Formula ThetaFormula() => Disp(All("r", N, All("A", Mat(FinR, R), All("tau", C,
        Equal(Call("theta", V("A"), V("tau")), Tsum("a", Arr(FinR, Z),
            ThetaTerm(V("A"), IntVec(FinR, V("a")))))))));
    private static Formula SummableFormula() => Disp(RankMatrix(UpperParameter(
        Summable("a", Arr(FinR, Z), Norm(ThetaTerm(V("A"), IntVec(FinR, V("a"))))))));
    private static Formula InversionFormula() => Disp(RankMatrix(UpperParameter(Equal(
        Call("theta", V("A"), Div(NegF(D(1)), V("tau"))),
        Mul(Mul(Pow(Mul(NegF(Imag), V("tau")), Div(Cast(V("r"), C), D(2))), DetFactor(V("A"))),
            Call("theta", Inv(V("A")), V("tau")))))));
}
