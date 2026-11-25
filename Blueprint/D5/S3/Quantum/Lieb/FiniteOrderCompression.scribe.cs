using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class FiniteOrderCompressionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Functional calculus in a positive corner", H("Functional calculus in a positive corner"), Blocks(
        Paragraph(Text("For every natural number n, MatrixMonotone(n,f) means that cfc(f,X) <= cfc(f,Y) for all positive semidefinite complex n by n matrices X <= Y. The calculus is the actual finite spectral functional calculus, and ReTr is the unnormalized real trace. zeroExtendedRatio(f) sends t to t/f(t), using total division, so its value at zero is zero. No continuity of this quotient at zero is implicit in the notation. Zero dimensions and singular noncommuting matrices are included wherever positivity is semidefinite. For a complete complex Hilbert space H, L(H) denotes continuous complex-linear endomorphisms, and corner is projection onto the first summand followed by inclusion. For a 2n by 2n matrix, firstCorner selects the coordinates finProdFinEquiv(0,i).")),
        Describe.Lean(DescribeId.Create("monotone-double-space-corner"), DeclarationHandle.Create("D5/S3/Quantum/Lieb/FiniteOrderCompression.monotone_double_space_corner"), H("One doubled Hilbert space suffices"), StatementSource.FromAuthor(Disp(All([B("H", Call("CompleteComplexHilbertType")), B("f", Fn), B("X", Call("L", Call("HSum", I("H"))))], Imp(And(Call("ContinuousOn", I("f"), Call("Ici", D(0))), And(Call("OperatorMonotone", Call("L", Call("HSum", I("H"))), I("f")), Leq(D(0), I("X")))), Leq(Call("corner", Cfc(I("f"), I("X"))), Cfc(I("f"), Call("corner", I("X")))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Let H be any complete complex Hilbert space and f be continuous on the nonnegative half-line. Monotonicity of f only on L(H direct sum H) implies that the first corner of f(X) is at most f of the first corner of every positive X. No sign condition on f(0) is needed. For each positive epsilon, a positive block diagonal operator dominates X with first block corner(X)+epsilon I. Its second block can depend on epsilon. Monotonicity and diagonal functional calculus give the perturbed bound; closedness of order and continuity remove epsilon."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("matrix-monotone-corner"), DeclarationHandle.Create("D5/S3/Quantum/Lieb/FiniteOrderCompression.matrix_monotone_corner"), H("The first corner at finite order 2n"), StatementSource.FromAuthor(Disp(All([B("n", Nat), B("f", Fn), B("X", Mat(Twice(I("n"))))], Imp(And(Call("ContinuousOn", I("f"), Call("Ici", D(0))), And(Mono(Twice(I("n")), I("f")), Pos(I("X")))), Leq(Call("firstCorner", Cfc(I("f"), I("X"))), Cfc(I("f"), Call("firstCorner", I("X")))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Choose an orthonormal coordinate equivalence between the doubled Euclidean Hilbert space and matrices indexed by Fin(2n). The equivalence preserves positivity, order and real functional calculus, so monotonicity at exactly order 2n supplies the doubled Hilbert-space hypothesis. The empty coordinate space is handled directly. Continuity is required on the closed nonnegative half-line; there is no positivity assumption on f(0)."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("matrix-monotone-contraction"), DeclarationHandle.Create("D5/S3/Quantum/Lieb/FiniteOrderCompression.matrix_monotone_contraction"), H("Contraction Jensen at doubled finite order"), StatementSource.FromAuthor(Disp(All([B("n", Nat), B("f", Fn), B("A", Mat(I("n"))), B("C", Mat(I("n")))], Imp(And(Call("ContinuousOn", I("f"), Call("Ici", D(0))), And(Leq(D(0), Call("apply", I("f"), D(0))), And(Mono(Twice(I("n")), I("f")), And(Pos(I("A")), Leq(Mul(Adj(I("C")), I("C")), D(1)))))), Leq(Mul(Mul(Adj(I("C")), Cfc(I("f"), I("A"))), I("C")), Cfc(I("f"), Mul(Mul(Adj(I("C")), I("A")), I("C")))))))), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/dinhhoaosakatoan2012powersstormer")), Blocks(Paragraph(Text("For every n, positive semidefinite A and contraction C, continuity of f, f(0)>=0 and matrix monotonicity at order 2n give C* f(A) C <= f(C* A C). A unitary dilation of C identifies this compression with the first corner of a conjugated positive block. The second block of f(diag(A,0)) contributes a nonnegative term, which may be discarded. This is the finite-order contraction argument of Hoa, Osaka and Toan, Lemma 2.1."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("matrix-monotone-restrict"), DeclarationHandle.Create("D5/S3/Quantum/Lieb/FiniteOrderCompression.matrix_monotone_restrict"), H("Restriction from doubled order"), StatementSource.FromAuthor(Disp(FinitePair(Imp(And(Mono(Twice(I("n")), I("f")), And(Pos(I("A")), And(Pos(I("B")), Leq(I("A"), I("B"))))), Leq(Cfc(I("f"), I("A")), Cfc(I("f"), I("B"))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Embed both n by n matrices as the first blocks of matrices on the direct sum. Congruence preserves their order, monotonicity applies after the coordinate equivalence, and rectangular spectral intertwining recovers f(A) and f(B) in the first corner. The restriction requires neither continuity nor a sign condition on f."))), DescribeRole.Theorem))));

    private static Formula I(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(I("R")));
    private static Formula Complex => Seq(Mathbb, Grp(I("C")));
    private static Formula Nat => Seq(Mathbb, Grp(I("N")));
    private static Formula Fn => new Formula.TypeArrow(Real, Real);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Mat(Formula n) => Call("Matrix", Fin(n), Fin(n), Complex);
    private static Formula Adj(Formula a) => Seq(a, Caret, Grp(Star));
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
    private static Formula FinitePair(Formula body) => All([B("n", Nat), B("f", Fn),
        B("A", Mat(I("n"))), B("B", Mat(I("n")))], body);
}
