using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class ZhangJingPowerCaseSettlementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/zhangjing2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The power block characterizes normality for 1/2 ≤ a < 1, including singular matrices; "
            + "at a = 1 it is positive semidefinite for every matrix.",
        H("The sharp upper endpoint of the Zhang–Jing power block"), Blocks(
            Entry("closed-interval", "claim", "The source's unresolved closed interval",
                Disp(Iff(V("claim"), Parenthesized(ClaimBody(false)))),
                "After Remark 2.13, p. 601: “Due to the limitations of our research method, we cannot "
                + "solve the problem that Theorem 2.3 holds for 1/2 ≤ a ≤ 1.” The proposition expands "
                + "the equivalence over every real a in that interval, every natural dimension n, "
                + "and every complex square matrix A. The matrix functions use Real.rpow, with x⁰ = 1. "
                + "PosSemidef means positive semidefinite, and normality means Aᴴ A = A Aᴴ.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("half-open-interval", "claimBelowOne", "The interval below the upper endpoint",
                Disp(Iff(V("claimBelowOne"), Parenthesized(ClaimBody(true)))),
                "The equivalence of Theorem 2.3 is restricted to 1/2 ≤ a < 1. Matrices may be singular, "
                + "and dimension zero is included. This is the positive portion of the source's "
                + "interval quoted after Remark 2.13 on p. 601.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("endpoint-refutation", "result", "The extension to a = 1 fails",
                Disp(Seq(Neg, Sp, Parenthesized(ClaimBody(false)))),
                "At a = 1 the diagonal corners are Aᴴ A and I, so the block is Qᴴ Q for Q = [A,I], "
                + "padded by zero rows to form a square matrix. It is positive semidefinite for every A. "
                + "For A = [[0,1],[2,0]], the (0,0) entries of Aᴴ A and A Aᴴ are 4 and 1. Thus A is "
                + "nonnormal and the universal equivalence on the closed interval is false.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Entry("below-endpoint", "below_one", "Normality is characterized below a = 1",
                Disp(ClaimBody(true)),
                "An SVD writes A = V D Wᴴ with nonnegative diagonal D. A unitary change of block "
                + "coordinates gives diagonal corners D^(2a) and Uᴴ D^(2(1−a)) U, where U = Wᴴ V. "
                + "Testing positivity with the column [-D^(1−2a),I] gives a positive semidefinite "
                + "difference Uᴴ D^(2(1−a)) U − D^(2(1−a)). Its trace is zero, so the difference "
                + "vanishes. Positive-exponent real-power injectivity on nonnegative singular values "
                + "forces U to commute with D, which is equivalent to normality. Conversely the "
                + "balanced block is the Gram matrix of [D^a,D^(1−a)]. The zero singular values obey "
                + "the same identities because a < 1. The cited lower interval 0 ≤ a ≤ 1/2 is outside "
                + "this theorem; infinite-dimensional operators are also outside its scope.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula ClaimBody(bool belowOne)
    {
        Formula a = V("a"), n = V("n"), matrix = V("A"), x = V("x");
        Formula first = Fun("x", Real(), new Formula.Power(x, Mul(D(2), a)));
        Formula second = Fun("x", Real(), new Formula.Power(x,
            Mul(D(2), Parenthesized(Sub(D(1), a)))));
        Formula equivalence = Iff(Call("Matrix.PosSemidef", Call("D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation.block", first, second, matrix)),
            Equal(Mul(Conj(matrix), matrix), Mul(matrix, Conj(matrix))));
        Formula upper = belowOne ? Lt(a, D(1)) : Leq(a, D(1));
        return All("a", Real(), Imp(Leq(new Formula.Fraction(D(1), D(2)), a),
            Imp(upper, All("n", Nat(), All("A", MatrixType(n), equivalence)))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula MatrixType(Formula n) => Call("Matrix", Call("Fin", n), Call("Fin", n), Complex());
    private static Formula Conj(Formula a) => Call("Matrix.conjTranspose", a);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(
        Seq(Operatorname, Grp(Seq(name.Split('.').Select((part, index) =>
            index == 0 ? V(part) : Seq(Dot, V(part))).ToArray()))), args);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Fun(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V("fun"), Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
}
