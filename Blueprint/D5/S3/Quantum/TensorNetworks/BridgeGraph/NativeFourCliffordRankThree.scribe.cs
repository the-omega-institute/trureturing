using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class NativeFourCliffordRankThreeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourCliffordRankThree";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Right dimension bound from the Pauli Clifford coefficient kernel.",
        H("Clifford coefficient kernels at width four"),
        Blocks(
            Describe.Lean(DescribeId.Create("pauli-clifford"),
                DeclarationHandle.Create(Owner + ".pauliClifford"), H("Pauli Clifford matrices"),
                StatementSource.FromAuthor(Disp(CliffordBasis())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The five matrices are written in tensor-product coordinates, with the first index " +
                    "ordered before the second. The Pauli matrices have off-diagonal entries one and one " +
                    "for sigma x, minus i and i for sigma y, and diagonal entries one and minus one " +
                    "for sigma z. Each unspecified entry is zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("clifford-kernel-four-bound"),
                DeclarationHandle.Create(Owner + ".clifford_kernel_four_bound"),
                H("Four-input to three-output dimension bound"),
                StatementSource.FromAuthor(Disp(CliffordBound())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The coefficient matrices of the right Gram differ from their normalized trace " +
                        "by elements of the compression kernel. After congruence these differences " +
                        "have two scalar diagonal blocks with opposite signs and two linked off-diagonal blocks.")),
                    Paragraph(Text(
                        "Diagonalizing the scalar trace on each pair makes the right factors within " +
                        "each pair orthogonal. A strict diagonal gap makes one factor injective. " +
                        "When the two gaps vanish, the cross blocks kill the common kernel of the first pair, " +
                        "so the second pair supplies two orthogonal injective extensions."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Apply(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula Bind(FormulaQuantifier q, string name, Formula type, Formula body) =>
        new Formula.Bind(q, FormulaIdentifier.Create(name), type, body);
    private static Formula All(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.Exists, name, type, body);
    private static Formula Parens(Formula formula) => Seq(Open, formula, Close);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parens(a), op, Parens(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Matrix(Formula rows, Formula cols) => Call("Matrix", rows, cols, V("Complex"));
    private static Formula Factors(Formula rows, Formula cols) =>
        new Formula.TypeArrow(Fin(D(4)), Matrix(Fin(rows), Fin(cols)));
    private static Formula Ct(Formula matrix) => Call("conjTranspose", matrix);

    private static Formula MatrixFour(params Formula[] entries) =>
        Seq(Begin, Grp(V("pmatrix")),
            entries[0], Amp, entries[1], Amp, entries[2], Amp, entries[3], RowBreak,
            entries[4], Amp, entries[5], Amp, entries[6], Amp, entries[7], RowBreak,
            entries[8], Amp, entries[9], Amp, entries[10], Amp, entries[11], RowBreak,
            entries[12], Amp, entries[13], Amp, entries[14], Amp, entries[15],
            End, Grp(V("pmatrix")));

    private static Formula CliffordBasis()
    {
        Formula z = D(0), o = D(1), n = Seq(Minus, o), i = Seq(Mathrm, Grp(V("i"))), ni = Seq(Minus, i);
        Formula Term(byte index, Formula matrix) => Eq(Call("pauliClifford", D(index)), matrix);
        return And(Term(0, MatrixFour(z, z, o, z, z, z, z, o, o, z, z, z, z, o, z, z)),
            And(Term(1, MatrixFour(z, z, ni, z, z, z, z, ni, i, z, z, z, z, i, z, z)),
            And(Term(2, MatrixFour(z, o, z, z, o, z, z, z, z, z, z, n, z, z, n, z)),
            And(Term(3, MatrixFour(z, ni, z, z, i, z, z, z, z, z, z, i, z, z, ni, z)),
                Term(4, MatrixFour(o, z, z, z, z, n, z, z, z, z, n, z, z, z, z, o))))));
    }

    private static Formula CliffordBound()
    {
        Formula a = V("a"), b = V("b"), c = V("c"), d = V("d"), lam = V("lambda");
        Formula X = V("X"), Y = V("Y"), i = V("i"), P = V("P"), T = V("T");
        Formula tensor = Seq(new Formula.Subscript(F.Sum, Seq(i, Colon, Fin(D(4)))), Sp,
            Call("kronecker", Apply(X, i), Apply(Y, i)));
        Formula cols = Call("Prod", Fin(b), Fin(c));
        Formula identity = Parens(Seq(D(1), Colon, Sp, Matrix(cols, cols)));
        Formula gram = Eq(Mul(Ct(tensor), tensor), Call("smul", Call("ofReal", lam), identity));
        Formula square = Matrix(Fin(D(4)), Fin(D(4)));
        Formula inSpan = Seq(Mul(Mul(Ct(P), T), P), Sp, InMacro, Sp,
            Call("span", V("Real"), Call("range", V("pauliClifford"))));
        Formula congruence = Some("P", square, And(Call("IsUnit", P), All("T", square,
            Implies(Call("IsHermitian", T), Implies(Eq(Call("compression", X, T), D(0)), inSpan)))));
        Formula bound = Le(Mul(D(4), c), Mul(D(3), d));
        Formula law = All("lambda", V("Real"), Implies(Lt(D(0), lam),
            Implies(Lt(a, b), Implies(gram, Implies(congruence, bound)))));
        return All("a", V("Nat"), All("b", V("Nat"), All("c", V("Nat"), All("d", V("Nat"),
            All("X", Factors(a, b), All("Y", Factors(d, c), law))))));
    }
}
