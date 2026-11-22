using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class NativeFourKernelDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourKernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spectral dimension bounds and rank-two coefficient spaces for a stack of four matrices.",
        H("Hermitian compression at width four"),
        Blocks(
            Describe.Lean(DescribeId.Create("compression"),
                DeclarationHandle.Create(Owner + ".compression"), H("Compression to the left stack"),
                StatementSource.FromAuthor(Disp(Compression())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Stacking the four left factors identifies the coefficient form on their common " +
                    "input by applying the coefficient matrix to the four copies of the output."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("compression-star"),
                DeclarationHandle.Create(Owner + ".compression_star"), H("Adjoint"),
                StatementSource.FromAuthor(Disp(Adjoint())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Taking the adjoint reverses the two multiplications by the stack."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hermitian-rank-bound"),
                DeclarationHandle.Create(Owner + ".hermitian_rank_bound"), H("Eigenvalue multiplicities"),
                StatementSource.FromAuthor(Disp(RankBound())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Projection to the nonpositive directions of a diagonalized coefficient form " +
                    "is injective on the range of the left stack. A vector killed by the projection " +
                    "would have strictly positive energy unless it vanished. Negating the coefficient " +
                    "form gives the other sign bound, and the two multiplicities sum to its rank."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coefficient-geometry"),
                DeclarationHandle.Create(Owner + ".coefficient_geometry"), H("Rank-two alternatives"),
                StatementSource.FromAuthor(Disp(Geometry())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A nonzero form of rank at most two has both signs. After congruence it has " +
                        "diagonal entries one, minus one, zero, zero. The three-by-three minors at the " +
                        "sum and difference of the diagonal form and an arbitrary Hermitian member " +
                        "give a zero lower block and equal outer products of the two upper rows " +
                        "of the off-diagonal block.")),
                    Paragraph(Text(
                        "If the first rows are proportional across the space, a common vector in " +
                        "the last two coordinates is killed by every member. If two first rows are " +
                        "independent, the rank-one condition on their sum forces the same row ratio " +
                        "throughout. The three-by-three minors then give a third neutral direction " +
                        "orthogonal to the common image of the off-diagonal blocks."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Bind(FormulaQuantifier q, string name, Formula type, Formula body) =>
        new Formula.Bind(q, FormulaIdentifier.Create(name), type, body);
    private static Formula All(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.Exists, name, type, body);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Matrix(Formula m, Formula n) => Call("Matrix", m, n, V("Complex"));
    private static Formula Square() => Matrix(Fin(D(4)), Fin(D(4)));
    private static Formula Parens(Formula p) => Seq(Open, p, Close);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parens(a), op, Parens(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Ct(Formula a) => Call("conjTranspose", a);
    private static Formula Compressed(Formula t) => Call("compression", V("X"), t);
    private static Formula ThroughStack(Formula body) =>
        All("a", V("Nat"), All("b", V("Nat"), All("X",
            new Formula.TypeArrow(Fin(D(4)), Matrix(Fin(V("a")), Fin(V("b")))), body)));
    private static Formula ForKernel(Formula body) =>
        All("T", Square(), Imp(Call("IsHermitian", V("T")),
            Imp(Eq(Compressed(V("T")), D(0)), body)));

    private static Formula Compression()
    {
        Formula S = Call("stackK", V("X"));
        Formula identity = Parens(Seq(D(1), Colon, Sp, Matrix(Fin(V("a")), Fin(V("a")))));
        return ThroughStack(All("T", Square(), Eq(Compressed(V("T")),
            Mul(Mul(Ct(S), Call("kronecker", V("T"), identity)), S))));
    }

    private static Formula Adjoint() => ThroughStack(All("T", Square(),
        Eq(Compressed(Ct(V("T"))), Ct(Compressed(V("T"))))));

    private static Formula RankBound()
    {
        Formula k = V("k"), T = V("T"), a = V("a"), b = V("b");
        Formula injective = Call("Injective", Call("mulVecLin", Call("stackK", V("X"))));
        return ThroughStack(Imp(injective, All("T", Square(),
            Imp(Call("IsHermitian", T), Imp(Eq(Compressed(T), D(0)), All("k", V("Nat"),
                Imp(Le(k, D(3)), Imp(Lt(Mul(k, a), b),
                    Lt(Call("rank", T), Sub(Mul(D(2), Sub(D(4), k)), D(1))))))))));
    }

    private static Formula Geometry()
    {
        Formula T = V("T"), E = V("E"), v = V("v");
        Formula rank = ForKernel(Le(Call("rank", T), D(2)));
        Formula zero = ForKernel(Eq(T, D(0)));
        Formula line = Some("v", new Formula.TypeArrow(Fin(D(4)), V("Complex")),
            And(Ne(v, D(0)), ForKernel(Eq(Call("mulVec", T, v), D(0)))));
        Formula neutral = Some("E", Matrix(Fin(D(4)), Fin(D(3))),
            And(Eq(Call("rank", E), D(3)), ForKernel(Eq(Mul(Mul(Ct(E), T), E), D(0)))));
        return ThroughStack(Imp(Call("LinearIndependent", V("Complex"), V("X")),
            Imp(rank, Or(zero, Or(line, neutral)))));
    }
}
