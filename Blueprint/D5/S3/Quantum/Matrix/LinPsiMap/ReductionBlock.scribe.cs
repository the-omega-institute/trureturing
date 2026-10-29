using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.LinPsiMap;

internal sealed class ReductionBlockDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016psimap");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reduction of a positive block supplies the reflected spectral comparison.",
        H("The map Psi and reduction-block positivity"), Blocks(
            Describe.Lean(DescribeId.Create("lin-psi-map"),
                DeclarationHandle.Create(Owner + "psi"),
                H("The trace reflection map"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every complex square matrix T, define Psi(T)=2 trace(T) I−T. The reduction map R(T)=trace(T) I−T is the related map used to construct the positive block in the argument."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lin-skew-matrix-unit"),
                DeclarationHandle.Create(Owner + "skew"),
                H("Antisymmetric matrix units"),
                StatementSource.FromAuthor(Disp(SkewFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For indices k and l in Fin n, subtract the matrix unit at (l,k) from the matrix unit at (k,l). This gives an antisymmetric complex matrix, which is zero when k equals l."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lin-skew-congruence-sum"),
                DeclarationHandle.Create(Owner + "skew_sum"),
                H("The sum of antisymmetric congruences"),
                StatementSource.FromAuthor(Disp(SkewSumFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex square matrix T, one half of the sum of skew(k,l) T skew(k,l)-adjoint over all ordered pairs equals trace(T) times the identity minus the transpose of T. The identity holds without symmetry or positivity assumptions on T."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lin-reduction-block-positivity"),
                DeclarationHandle.Create(Owner + "reduction_block_posSemidef"),
                H("Positivity of the reduction block"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let the complex block matrix [A X; X-adjoint B] be positive semidefinite. Then [R(A) R(X-adjoint); R(X) R(B)] is positive semidefinite, in every finite dimension and without commutation or rank assumptions.")),
                    Paragraph(Text("For coordinate indices k and l, form the antisymmetric matrix F from the two matrix units at (k,l) and (l,k). One half of the sum of F T F-adjoint over all ordered pairs is trace(T) I−transpose(T). Apply these congruences simultaneously in both diagonal blocks to the transpose of the original positive block. The resulting positive sum has exactly the stated four blocks."))),
                DescribeRole.Theorem))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula QCall(string owner, string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(X(owner), Dot, X(name))), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(F.Open, value, F.Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula NumberType(string name) => Seq(Mathbb, Grp(X(name)));
    private static Formula FinType() => Call("Fin", X("n"));
    private static Formula MatrixType() => Call("Matrix", FinType(), FinType(), NumberType("C"));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Smul(Formula scalar, Formula matrix) => QCall("HSMul", "hSMul", scalar, matrix);
    private static Formula SumOver(string name, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), FinType())), Sp, body);

    private static Formula SkewFormula()
    {
        var one = Typed(D(1), NumberType("C"));
        return All("n", NumberType("N"), All("k", FinType(), All("l", FinType(),
            Equal(Call("skew", X("k"), X("l")),
                Subtract(QCall("Matrix", "single", X("k"), X("l"), one),
                    QCall("Matrix", "single", X("l"), X("k"), one))))));
    }

    private static Formula SkewSumFormula()
    {
        var skew = Call("skew", X("k"), X("l"));
        var half = QCall("Complex", "ofReal", Typed(new Formula.Fraction(D(1), D(2)), NumberType("R")));
        var sum = SumOver("k", SumOver("l",
            Multiply(Multiply(skew, X("T")), QCall("Matrix", "conjTranspose", skew))));
        return All("n", NumberType("N"), All("T", MatrixType(),
            Equal(Smul(half, Parenthesized(sum)),
                Subtract(Smul(QCall("Matrix", "trace", X("T")), Typed(D(1), MatrixType())),
                    QCall("Matrix", "transpose", X("T"))))));
    }
}
