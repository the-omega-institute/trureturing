using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class PeritoTensorBlockBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/PeritoTensorBlockBound.";
    private static readonly Formula N = F.Id("n"), M = F.Id("m"), Dd = F.Id("d"),
        C = F.Id("c"), B = F.Id("B"), U = F.Id("U"), K = F.Id("K"),
        Y = F.Id("y"), I = F.Id("i"), Z = F.Id("z");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unitary tensor sums satisfy the uniform scalar coefficient bound on the unit circle in the Euclidean operator norm, for all finite dimensions and all finite numbers of summands.",
        H("Unitary spectral blocks and the tensor bound"),
        Blocks(
            Paragraph(Text(
                "All matrix norms below are operator norms for the Euclidean vector norm. " +
                "The local spaces have dimensions n and m, and the summation index is Fin d. " +
                "The dimensions and d may be zero. The symbol kronecker denotes the " +
                "matrix tensor product, and unitaryGroup is the group of complex matrices " +
                "whose conjugate transpose is their inverse.")),
            Describe.Lean(
                DescribeId.Create("diagonal-tensor-blocks-have-a-uniform-norm-bound"),
                DeclarationHandle.Create(Prefix + "norm_diagonal_tensor_sum_le"),
                H("Uniform diagonal block bound"),
                StatementSource.FromAuthor(Disp(DiagonalBound())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let c be a complex coefficient array and let every B(y) be unitary. " +
                        "Suppose K is nonnegative and, for every i, the sum of the moduli " +
                        "of c(y)(i) is at most K. The tensor sum of diagonal(c(y)) with B(y) " +
                        "then has operator norm at most K.")),
                    Paragraph(Text(
                        "Write a vector as Bob-vector rows v(i). The i-th output row is " +
                        "the sum of c(y)(i) times B(y)v(i). The triangle inequality and " +
                        "unitary norm preservation bound its norm by K times the norm " +
                        "of v(i). Summing the squared row norms bounds the squared total " +
                        "norm by K squared times the squared input norm. Nonnegativity " +
                        "of K permits taking square roots."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unit-circle-coefficients-bound-the-unitary-tensor-sum"),
                DeclarationHandle.Create(Prefix + "tensor_block_bound"),
                H("Unit-circle bound for a unitary tensor sum"),
                StatementSource.FromAuthor(Disp(UnitaryBound())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive d, the phase windowRoot(d) is exp(2 pi i/d); " +
                        "for d = 0 the sum is empty. If U and all B(y) " +
                        "are unitary, and the sum of |1 + windowRoot(d)^y z| is at most " +
                        "K for every complex z of modulus one, the tensor sum of " +
                        "I + windowRoot(d)^y U with B(y) has operator norm at most K. " +
                        "The scalar hypothesis at z = 1 already implies K is nonnegative.")),
                    Paragraph(Text(
                        "A unitary matrix is normal. Its commuting Hermitian real and " +
                        "imaginary parts have orthogonal joint eigenspaces spanning the " +
                        "space, and an orthonormal basis subordinate to these spaces " +
                        "diagonalizes U. If P is the resulting unitary basis matrix, " +
                        "P adjoint times U times P is diagonal(z). Unitarity of this " +
                        "diagonal matrix gives |z(i)| = 1 for every i.")),
                    Paragraph(Text(
                        "Conjugation by P tensor I turns the tensor sum into diagonal " +
                        "blocks with coefficients 1 + windowRoot(d)^y z(i). The scalar " +
                        "hypothesis bounds each coefficient sum. The diagonal block " +
                        "estimate applies, and unitary conjugation preserves operator " +
                        "norm. Consequently its action on a vector v has norm at most " +
                        "K times the norm of v; Cauchy-Schwarz also bounds the modulus " +
                        "of its pairing with w by K times the norms of w and v."))),
                DescribeRole.Theorem))));

    private static Formula DiagonalBound() => Dimensions(
        All(C, Arrow(Fin(Dd), Arrow(Fin(N), Complex())),
        All(B, Arrow(Fin(Dd), Mat(M)), All(K, Real(),
            Imp(UnitaryFamily(), Imp(Le(D(0), K),
            Imp(All(I, Fin(N), Le(SumOver(Y, Fin(Dd), Norm(App(App(C, Y), I))), K)),
                Le(Norm(SumOver(Y, Fin(Dd),
                    Call("kronecker", Call("diagonal", App(C, Y)), App(B, Y)))), K))))))));

    private static Formula UnitaryBound() => Dimensions(
        All(U, Mat(N), All(B, Arrow(Fin(Dd), Mat(M)), All(K, Real(),
            Imp(Member(U, Call("unitaryGroup", Fin(N), Complex())),
            Imp(UnitaryFamily(),
            Imp(All(Z, Complex(), Imp(Eq(Norm(Z), D(1)),
                Le(SumOver(Y, Fin(Dd), Norm(Add(D(1), Mul(Phase(), Z)))), K))),
                Le(Norm(SumOver(Y, Fin(Dd),
                    Call("kronecker", Add(D(1), Mul(Phase(), U)), App(B, Y)))), K))))))));

    private static Formula Dimensions(Formula body) =>
        All(N, Naturals(), All(M, Naturals(), All(Dd, Naturals(), body)));
    private static Formula UnitaryFamily() => All(Y, Fin(Dd),
        Member(App(B, Y), Call("unitaryGroup", Fin(M), Complex())));
    private static Formula Phase() => new Formula.Power(Call("windowRoot", Dd), Y);
    private static Formula SumOver(Formula name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(name, Sp, InMacro, Sp, type), Sp, body);
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, name, Sp, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(Open, a, Sp, To, Sp, b, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Mat(Formula dimension) => Call("Matrix", Fin(dimension), Fin(dimension), Complex());
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(
        Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
}
