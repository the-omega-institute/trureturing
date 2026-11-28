using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.Spectral;

internal sealed class IsometricCalculusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Isometries, functional calculus and unitary dilations", H("Isometries, functional calculus and unitary dilations"), Blocks(
        Paragraph(Text("FiniteType denotes an arbitrary finite type with decidable equality. All matrices use complex scalars. Adjoint is conjugate transpose. Functional calculus is defined by the finite spectrum, so an arbitrary real function is continuous on the required spectrum. The two rectangular results are the congruence and spectral intertwining results for positive-map Jensen. The dilation is the orthonormal-basis extension construction for contractions.")),
        Describe.Lean(DescribeId.Create("congruence-mono"), DeclarationHandle.Create("D5/S3/Quantum/Matrix/Spectral/IsometricCalculus.congruence_mono"), H("Rectangular congruence preserves order"), StatementSource.FromAuthor(Disp(All([B("n", I("FiniteType")), B("m", I("FiniteType")), B("A", Call("Matrix", I("n"), I("n"), Complex)), B("B", Call("Matrix", I("n"), I("n"), Complex)), B("V", Call("Matrix", I("n"), I("m"), Complex))], Imp(Leq(I("A"), I("B")), Leq(Mul(Mul(Adj(I("V")), I("A")), I("V")), Mul(Mul(Adj(I("V")), I("B")), I("V"))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For arbitrary finite coordinate types n and m, A <= B implies V* A V <= V* B V for every rectangular V. Apply positive-semidefinite congruence to B-A."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("cfc-intertwining"), DeclarationHandle.Create("D5/S3/Quantum/Matrix/Spectral/IsometricCalculus.cfc_intertwining"), H("Rectangular spectral intertwining"), StatementSource.FromAuthor(Disp(All([B("n", I("FiniteType")), B("m", I("FiniteType")), B("A", Call("Matrix", I("n"), I("n"), Complex)), B("B", Call("Matrix", I("m"), I("m"), Complex)), B("V", Call("Matrix", I("n"), I("m"), Complex)), B("f", Fn)], Imp(And(Herm(I("A")), And(Herm(I("B")), Eqn(Mul(I("A"), I("V")), Mul(I("V"), I("B"))))), Eqn(Mul(Cfc(I("f"), I("A")), I("V")), Mul(I("V"), Cfc(I("f"), I("B")))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("If Hermitian A and B satisfy A V=V B, then f(A)V=V f(B) for every real function f. In eigenvector coordinates, each coefficient of V is annihilated by the difference of the corresponding eigenvalues. Equal eigenvalues give equal function values; unequal ones force that coefficient to vanish."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("exists-unitary-dilation"), DeclarationHandle.Create("D5/S3/Quantum/Matrix/Spectral/IsometricCalculus.exists_unitary_dilation"), H("A contraction is a corner of a unitary"), StatementSource.FromAuthor(Disp(All([B("n", Nat), B("C", Mat(I("n")))], Imp(Pos(Sub(D(1), Mul(Adj(I("C")), I("C")))), Some([B("U", Call("Matrix", Call("Sum", Fin(I("n")), Fin(I("n"))), Call("Sum", Fin(I("n")), Fin(I("n"))), Complex))], And(Call("Unitary", I("U")), All([B("i", Fin(I("n"))), B("j", Fin(I("n")))], Eqn(Call("entry", I("U"), Call("inl", I("i")), Call("inl", I("j"))), Call("entry", I("C"), I("i"), I("j")))))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every complex n by n C with I-C* C positive semidefinite, there is a unitary U on Fin n direct sum Fin n whose upper-left block is C. Stack the columns of C above those of sqrt(I-C* C). Their Gram matrix is I, so the resulting orthonormal family extends to an orthonormal basis. The change-of-basis matrix gives U, including the empty case n=0."))), DescribeRole.Theorem))));

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
    private static Formula Some(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. vars], body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Pos(Formula a) => Call("PosSemidef", a);
    private static Formula Herm(Formula a) => Call("IsHermitian", a);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Cfc(Formula f, Formula a) => Call("cfc", f, a);
}
