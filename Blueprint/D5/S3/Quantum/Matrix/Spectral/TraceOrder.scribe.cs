using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.Spectral;

internal sealed class TraceOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Positivity and monotonicity of matrix traces", H("Positivity and monotonicity of matrix traces"), Blocks(
        Paragraph(Text("FiniteType denotes a finite coordinate type with decidable equality. ReTr means the real part of the ordinary unnormalized matrix trace. The positive-product trace argument is the RHLinalg spectral proof from the attributed Zeta23 source; the weighted-order consequence is the positive-trace argument for inverse trace convexity.")),
        Describe.Lean(DescribeId.Create("trace-mul-nonneg-of-possemidef"), DeclarationHandle.Create("D5/S3/Quantum/Matrix/Spectral/TraceOrder.trace_mul_nonneg_of_posSemidef"), H("Positive products have nonnegative real trace"), StatementSource.FromAuthor(Disp(All([B("k", I("RCLike")), B("n", I("FiniteType")), B("A", Call("Matrix", I("n"), I("n"), I("k"))), B("B", Call("Matrix", I("n"), I("n"), I("k")))], Imp(And(Pos(I("A")), Pos(I("B"))), Leq(D(0), Tr(Mul(I("A"), I("B")))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For positive semidefinite A and B over any RCLike scalar type, ReTr(A B)>=0. Diagonalize A and cycle the trace. Each summand is a nonnegative eigenvalue of A times a nonnegative diagonal entry of a unitary conjugate of B. Neither A B nor B A is required to be Hermitian."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("weighted-trace-re-mono"), DeclarationHandle.Create("D5/S3/Quantum/Matrix/Spectral/TraceOrder.weighted_trace_re_mono"), H("A positive weight preserves trace order"), StatementSource.FromAuthor(Disp(All([B("n", I("FiniteType")), B("A", Call("Matrix", I("n"), I("n"), Complex)), B("B", Call("Matrix", I("n"), I("n"), Complex)), B("C", Call("Matrix", I("n"), I("n"), Complex))], Imp(And(Pos(I("C")), Leq(I("A"), I("B"))), Leq(Tr(Mul(I("C"), I("A"))), Tr(Mul(I("C"), I("B")))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every positive semidefinite complex C and A <= B, ReTr(C A)<=ReTr(C B). The difference is ReTr(C(B-A)), which is nonnegative by positive-product trace positivity. No separate Hermitian hypothesis on A or B is required."))), DescribeRole.Theorem))));

    private static Formula I(string name) => F.Id(name);
    private static Formula Complex => Seq(Mathbb, Grp(I("C")));
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
    private static Formula Tr(Formula a) => Call("ReTr", a);
}
