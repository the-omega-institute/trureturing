using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb.FiniteOrder;

internal sealed class PowersStormerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The finite-order generalized Powers-Stormer inequality", H("The finite-order generalized Powers-Stormer inequality"), Blocks(
        Paragraph(Text("For every natural number n, MatrixMonotone(n,f) means that cfc(f,X) <= cfc(f,Y) for all positive semidefinite complex n by n matrices X <= Y. The calculus is the actual finite spectral functional calculus, and ReTr is the unnormalized real trace. zeroExtendedRatio(f) sends t to t/f(t), using total division, so its value at zero is zero. No continuity of this quotient at zero is implicit in the notation. Zero dimensions and singular noncommuting matrices are included wherever positivity is semidefinite. The hypotheses on f are continuity on [0,infinity) and f(t)>0 for every t>0. Right continuity then gives f(0)>=0. The trace norm is ReTr(sqrt(M* M)); it is not divided by the dimension or by two.")),
        Describe.Lean(DescribeId.Create("generalized-powers-stormer"), DeclarationHandle.Create("D5/S3/Quantum/Lieb/FiniteOrder/PowersStormer.generalized_powers_stormer"), H("The full singular trace inequality"), StatementSource.FromAuthor(Disp(FinitePair(Imp(And(Hyp(I("f")), And(Mono(Twice(I("n")), I("f")), And(Pos(I("A")), Pos(I("B"))))), Leq(Sub(Add(Tr(I("A")), Tr(I("B"))), Call("traceNorm", Sub(I("A"), I("B")))), Mul(D(2), Tr(Mul(Mul(Call("sqrt", Cfc(I("f"), I("A"))), Cfc(Ratio(I("f")), I("B"))), Call("sqrt", Cfc(I("f"), I("A"))))))))))), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/dinhhoaosakatoan2012powersstormer")), Blocks(Paragraph(Text("Hoa, Osaka and Toan, Theorem 2.1, gives this inequality with factor two for the unnormalized canonical trace. Take the single common upper bound C=B+posPart(A-B)=A+negPart(A-B). Both f and its zero-extended ratio are monotone at order n. Positivity of trace pairings, the identities f(X)g(X)=X and a common-roof estimate yield ReTr(A)-(ReTr(C)-ReTr(B)) <= ReTr(f(A)g(B)). The Jordan trace-norm identity converts the left side into half the asserted trace deficit. Trace cyclicity converts the crossed product to the displayed positive sandwich. The construction keeps the same C in every comparison and requires neither commutativity nor invertibility."))), DescribeRole.Theorem))));

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
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Cfc(Formula f, Formula a) => Call("cfc", f, a);
    private static Formula Tr(Formula a) => Call("ReTr", a);
    private static Formula Twice(Formula n) => Mul(D(2), n);
    private static Formula Mono(Formula n, Formula f) => Call("MatrixMonotone", n, f);
    private static Formula Hyp(Formula f) => And(Call("ContinuousOn", f, Call("Ici", D(0))),
        All([B("t", Real)], Imp(Seq(D(0), Lt, I("t")), Seq(D(0), Lt, Call("apply", f, I("t"))))));
    private static Formula Ratio(Formula f) => Call("zeroExtendedRatio", f);
    private static Formula FinitePair(Formula body) => All([B("n", Nat), B("f", Fn),
        B("A", Mat(I("n"))), B("B", Mat(I("n")))], body);
}
