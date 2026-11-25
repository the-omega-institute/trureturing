using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb.FiniteOrder;

internal sealed class SingularRatioDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Monotonicity of the zero-extended ratio", H("Monotonicity of the zero-extended ratio"), Blocks(
        Paragraph(Text("For every natural number n, MatrixMonotone(n,f) means that cfc(f,X) <= cfc(f,Y) for all positive semidefinite complex n by n matrices X <= Y. The calculus is the actual finite spectral functional calculus, and ReTr is the unnormalized real trace. zeroExtendedRatio(f) sends t to t/f(t), using total division, so its value at zero is zero. No continuity of this quotient at zero is implicit in the notation. Zero dimensions and singular noncommuting matrices are included wherever positivity is semidefinite.")),
        Describe.Lean(DescribeId.Create("ratio-monotone-possemidef"), DeclarationHandle.Create("D5/S3/Quantum/Lieb/FiniteOrder/SingularRatio.ratio_monotone_posSemidef"), H("Ratio monotonicity on the closed positive cone"), StatementSource.FromAuthor(Disp(FinitePair(Imp(And(Hyp(I("f")), And(Mono(Twice(I("n")), I("f")), And(Pos(I("A")), And(Pos(I("B")), Leq(I("A"), I("B")))))), Leq(Cfc(Ratio(I("f")), I("A")), Cfc(Ratio(I("f")), I("B"))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The ratio is monotone on the entire positive semidefinite cone, including a zero eigenvalue and functions vanishing at zero. First replace f by f+epsilon. A positive scalar shift of A and B permits the positive-definite ratio theorem; continuity of the regularized ratio then removes that shift. Finally epsilon tends to zero. On each fixed finite spectrum, the value at zero is identically zero and every positive spectral point has f(t)>0, so pointwise convergence suffices. Continuity of the original ratio at zero is not required."))), DescribeRole.Theorem))));

    private static Formula I(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(I("R")));
    private static Formula Complex => Seq(Mathbb, Grp(I("C")));
    private static Formula Nat => Seq(Mathbb, Grp(I("N")));
    private static Formula Fn => new Formula.TypeArrow(Real, Real);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Mat(Formula n) => Call("Matrix", Fin(n), Fin(n), Complex);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula.BoundVariable B(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Pos(Formula a) => Call("PosSemidef", a);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Cfc(Formula f, Formula a) => Call("cfc", f, a);
    private static Formula Twice(Formula n) => Mul(D(2), n);
    private static Formula Mono(Formula n, Formula f) => Call("MatrixMonotone", n, f);
    private static Formula Hyp(Formula f) => And(Call("ContinuousOn", f, Call("Ici", D(0))),
        All([B("t", Real)], Imp(Seq(D(0), Lt, I("t")), Seq(D(0), Lt, Call("apply", f, I("t"))))));
    private static Formula Ratio(Formula f) => Call("zeroExtendedRatio", f);
    private static Formula FinitePair(Formula body) => All([B("n", Nat), B("f", Fn),
        B("A", Mat(I("n"))), B("B", Mat(I("n")))], body);
}
