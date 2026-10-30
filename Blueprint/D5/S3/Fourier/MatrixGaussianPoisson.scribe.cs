using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class MatrixGaussianPoissonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every natural rank r, real positive definite A and complex b with positive real part, sum_a exp(-pi b Q_A(a)) equals sqrt(det A)^(-1) b^(-r/2) sum_k exp(-pi Q_(A^(-1))(k)/b), with a and k ranging over all integer vectors of rank r. Both primal and inverse-form term norms are summable. The power is principal. The proof uses coordinate Poisson summation, the genuine matrix Fourier integral and absolute convergence of both lattice sums. No integer-coordinate diagonalization is used, and rank zero remains in scope.",
        H("MatrixGaussianPoisson"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("matrixgaussianpoisson-exists-quadratic-lower-bound"),
                DeclarationHandle.Create("D5/S3/Fourier/MatrixGaussianPoisson.exists_quadratic_lower_bound"),
                H("Positive coordinate coercivity"),
                StatementSource.FromAuthor(LowerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural rank r and real positive definite matrix A on Fin r, there is a real t>0 such that t sum_i x_i^2 <= Q_A(x) for every real vector x. For nonempty coordinates Cauchy-Schwarz for A^(-1) gives the reciprocal inverse-trace constant. Empty coordinates are handled separately and require no positive inverse trace."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matrixgaussianpoisson-summable-norm-gaussian"),
                DeclarationHandle.Create("D5/S3/Fourier/MatrixGaussianPoisson.summable_norm_gaussian"),
                H("Absolute integer-vector Gaussian convergence"),
                StatementSource.FromAuthor(SummableFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural rank r, real positive definite matrix A and complex b with positive real part, the norms of exp(-pi b Q_A(a)) are summable over all integer vectors a. Applying the same theorem to A^(-1) and b^(-1) supplies the dual norm sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matrixgaussianpoisson-gaussianmap"),
                DeclarationHandle.Create("D5/S3/Fourier/MatrixGaussianPoisson.gaussianMap"),
                H("Continuous coordinate Gaussian"),
                StatementSource.FromAuthor(MapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The continuous map x -> exp(-pi b Q_A(x)) is defined on real coordinate space for every real matrix A and complex b."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("matrixgaussianpoisson-locally-summable-norm-gaussian"),
                DeclarationHandle.Create("D5/S3/Fourier/MatrixGaussianPoisson.locally_summable_norm_gaussian"),
                H("Locally normal integer periodization"),
                StatementSource.FromAuthor(LocalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural rank r, real positive definite A, complex b with positive real part and compact K in real coordinate space, the sup norms on K of the integer translates of the Gaussian form a summable family. Coordinate coercivity and (x+a)^2 >= a^2/2-x^2 give a uniform summable product majorant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matrixgaussianpoisson-poisson-gaussian"),
                DeclarationHandle.Create("D5/S3/Fourier/MatrixGaussianPoisson.poisson_gaussian"),
                H("General positive-matrix Gaussian Poisson identity"),
                StatementSource.FromAuthor(PoissonFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural rank r, real positive definite A and complex b with positive real part, sum_a exp(-pi b Q_A(a)) equals sqrt(det A)^(-1) b^(-r/2) sum_k exp(-pi Q_(A^(-1))(k)/b), with a and k ranging over all integer vectors of rank r. Both primal and inverse-form term norms are summable. The power is principal. The proof uses coordinate Poisson summation, the genuine matrix Fourier integral and absolute convergence of both lattice sums. No integer-coordinate diagonalization is used, and rank zero remains in scope."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Z => Seq(Mathbb, Grp(V("Z")));
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Some(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Pos(Formula a) => new Formula.Relation(D(0), FormulaRelationOperator.LessThan, a);
    private static Formula LeqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
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
    private static Formula G(Formula a, Formula b, Formula x) => ExpF(Mul(Mul(NegF(Pi), b), Cast(Q(a, x), C)));
    private static Formula DualG(Formula a, Formula b, Formula x) => ExpF(Mul(Div(NegF(Pi), b), Cast(Q(Inv(a), x), C)));
    private static Formula PositiveMatrix(Formula n, Formula p) => All("A", Mat(n, R), Imp(Call("PosDef", V("A")), p));
    private static Formula RightParameter(Formula p) => All("b", C, Imp(Pos(Call("re", V("b"))), p));
    private static Formula RankMatrix(Formula p) => All("r", N, PositiveMatrix(FinR, p));
    private static Formula DetFactor(Formula a) => Inv(Cast(Call("sqrt", Call("det", a)), C));

    private static Formula LowerFormula() => Disp(RankMatrix(Some("t", R, And(Pos(V("t")),
        All("x", Arr(FinR, R), LeqF(Mul(V("t"), Call("sum", Lam("i", FinR,
            Pow(At(V("x"), V("i")), D(2))))), Q(V("A"), V("x"))))))));
    private static Formula SummableFormula() => Disp(RankMatrix(RightParameter(
        Summable("a", Arr(FinR, Z), Norm(G(V("A"), V("b"), IntVec(FinR, V("a"))))))));
    private static Formula MapFormula() => Disp(All("r", N, All("A", Mat(FinR, R), All("b", C,
        All("x", Arr(FinR, R), Equal(At(Call("gaussianMap", V("A"), V("b")), V("x")),
            G(V("A"), V("b"), V("x"))))))));
    private static Formula LocalFormula() => Disp(RankMatrix(RightParameter(All("K", Call("Compacts", Arr(FinR, R)),
        Summable("a", Arr(FinR, Z), Norm(Call("restrict", Call("comp", Call("gaussianMap", V("A"), V("b")),
            Call("addRight", IntVec(FinR, V("a")))), V("K"))))))));
    private static Formula PoissonFormula()
    {
        Formula primal = G(V("A"), V("b"), IntVec(FinR, V("a")));
        Formula dual = DualG(V("A"), V("b"), IntVec(FinR, V("k")));
        Formula factor = Mul(DetFactor(V("A")), Pow(V("b"), Div(NegF(Cast(V("r"), C)), D(2))));
        return Disp(RankMatrix(RightParameter(And(Summable("a", Arr(FinR, Z), Norm(primal)),
            And(Summable("k", Arr(FinR, Z), Norm(dual)),
                Equal(Tsum("a", Arr(FinR, Z), primal), Mul(factor, Tsum("k", Arr(FinR, Z), dual))))))));
    }
}
