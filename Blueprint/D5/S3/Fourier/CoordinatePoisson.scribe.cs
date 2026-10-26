using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class CoordinatePoissonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let n be any finite coordinate type and f a continuous complex function on real coordinate space. Assume f is integrable for coordinate Lebesgue measure, its integer translates have summable sup norms on every compact set, and the integer samples of its negative-exponent Fourier integral are summable. Then sum over integer vectors a of f(a) equals sum over integer vectors k of the integral of exp(-2 pi i sum_j k_j x_j) f(x). The unit cube is an actual fundamental domain for integer translations. Local normal convergence justifies descent to the unit torus and dominated sum-integral interchange; the torus Fourier series reconstructs the value at zero.",
        H("CoordinatePoisson"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coordinatepoisson-tsum-eq-tsum-integral"),
                DeclarationHandle.Create("D5/S3/Fourier/CoordinatePoisson.tsum_eq_tsum_integral"),
                H("Coordinate Poisson summation"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let n be any finite coordinate type and f a continuous complex function on real coordinate space. Assume f is integrable for coordinate Lebesgue measure, its integer translates have summable sup norms on every compact set, and the integer samples of its negative-exponent Fourier integral are summable. Then sum over integer vectors a of f(a) equals sum over integer vectors k of the integral of exp(-2 pi i sum_j k_j x_j) f(x). The unit cube is an actual fundamental domain for integer translations. Local normal convergence justifies descent to the unit torus and dominated sum-integral interchange; the torus Fourier series reconstructs the value at zero."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Imag => Seq(Operatorname, Grp(V("Complex")), Dot, Operatorname, Grp(V("I")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Z => Seq(Mathbb, Grp(V("Z")));
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula NegF(Formula a) => new Formula.Negate(a);
    private static Formula Cast(Formula a, Formula t) => Seq(Open, a, Colon, t, Close);
    private static Formula Lam(string s, Formula t, Formula p) => Seq(Open, V(s), Colon, t, Sp, Mapsto, Sp, p, Close);
    private static Formula At(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula ExpF(Formula x) => Call("exp", x);
    private static Formula IntVec(Formula n, Formula a) => Lam("i", n, Cast(At(a, V("i")), R));
    private static Formula Tsum(string s, Formula t, Formula p) => Call("tsum", Lam(s, t, p));
    private static Formula Summable(string s, Formula t, Formula p) => Call("Summable", Lam(s, t, p));
    private static Formula Integral(string s, Formula t, Formula p) => Call("integral", Lam(s, t, p), Call("volume", t));
    private static Formula Inst(string cls, Formula n) => Seq(OpenBracket, Call(cls, n), CloseBracket, Sp);

    private static Formula TheoremFormula()
    {
        Formula n = V("n"), realSpace = Arr(n, R), intSpace = Arr(n, Z);
        Formula phase = ExpF(Mul(Mul(Mul(NegF(D(2)), Pi), Imag), Cast(Call("sum",
            Lam("i", n, Mul(Cast(At(V("k"), V("i")), R), At(V("x"), V("i"))))), C)));
        Formula coeff = Integral("x", realSpace, Mul(phase, At(V("f"), V("x"))));
        Formula local = All("K", Call("Compacts", realSpace), Summable("a", intSpace,
            Norm(Call("restrict", Call("comp", V("f"), Call("addRight", IntVec(n, V("a")))), V("K")))));
        Formula assumptions = And(Call("Integrable", V("f"), Call("volume", realSpace)),
            And(local, Summable("k", intSpace, coeff)));
        Formula law = Equal(Tsum("a", intSpace, At(V("f"), IntVec(n, V("a")))), Tsum("k", intSpace, coeff));
        return Disp(All("n", V("Type"), Seq(Inst("Fintype", n),
            All("f", Call("ContinuousMap", realSpace, C), Imp(assumptions, law)))));
    }
}
