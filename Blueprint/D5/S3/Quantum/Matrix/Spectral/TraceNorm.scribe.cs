using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.Spectral;

internal sealed class TraceNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The matrix trace norm and Hermitian Jordan mass", H("The matrix trace norm and Hermitian Jordan mass"), Blocks(
        Paragraph(Text("RCLike is the real-or-complex scalar interface. FiniteType denotes a finite coordinate type with decidable equality; FintypeType assumes finiteness alone. ReTr is the real part of the unnormalized trace; square roots, positive parts and negative parts use the spectral matrix calculus. The rectangular trace-norm definition is the attributed Physlib definition, and the Hermitian identity uses the canonical spectral positive and negative parts.")),
        Describe.Lean(DescribeId.Create("tracenorm"), DeclarationHandle.Create("D5/S3/Quantum/Matrix/Spectral/TraceNorm.traceNorm"), H("The actual rectangular trace norm"), StatementSource.FromAuthor(Disp(All([B("m", I("FintypeType")), B("n", I("FintypeType")), B("k", I("RCLike")), B("A", Call("Matrix", I("m"), I("n"), I("k")))], Eqn(Call("traceNorm", I("A")), Tr(Call("sqrt", Mul(Adj(I("A")), I("A")))))))), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/wilde2017quantum")), Blocks(Paragraph(Text("For any finite row and column types and any RCLike scalar type, traceNorm(A) is ReTr(sqrt(A* A)). Only finiteness is required by this definition; no decidable equality, square shape, normalization or invertibility is assumed."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("trace-norm-jordan-mass"), DeclarationHandle.Create("D5/S3/Quantum/Matrix/Spectral/TraceNorm.trace_norm_jordan_mass"), H("The positive and negative masses add"), StatementSource.FromAuthor(Disp(All([B("n", I("FiniteType")), B("A", Call("Matrix", I("n"), I("n"), Complex))], Imp(Herm(I("A")), Eqn(Call("traceNorm", I("A")), Add(Tr(Call("posPart", I("A"))), Tr(Call("negPart", I("A"))))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every Hermitian complex square matrix A on a finite decidable coordinate type, traceNorm(A)=ReTr(posPart(A))+ReTr(negPart(A)). Spectral absolute value equals the sum of these two positive parts, and its trace is the trace norm. The identity includes singular matrices and the empty type."))), DescribeRole.Theorem))));

    private static Formula I(string name) => F.Id(name);
    private static Formula Complex => Seq(Mathbb, Grp(I("C")));
    private static Formula Adj(Formula a) => Seq(a, Caret, Grp(Star));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula.BoundVariable B(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Herm(Formula a) => Call("IsHermitian", a);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Tr(Formula a) => Call("ReTr", a);
}
