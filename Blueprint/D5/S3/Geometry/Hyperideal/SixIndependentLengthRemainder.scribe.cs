using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class SixIndependentLengthRemainderDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Geometry/Hyperideal/SixIndependentLengthRemainder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact determinant remainder for the six-independent-length character coordinates.",
        H("The six-independent-length determinant remainder"),
        Blocks(
            Paragraph(Text(
                "The variables r, o, A, B, xi and zeta are real. The matrix gram is the "
                + "four-by-four character-coordinate Gram matrix for the six independent "
                + "length slice. The factors L and M are the two symmetric-center block "
                + "determinants, while Xi is the exact quadratic-plus-quartic asymmetry "
                + "remainder.")),
            Node("determinant-remainder-identity",
                "Exact determinant remainder",
                "determinant_remainder_identity",
                StatementIdentity(),
                "Expanding the determinant in the character coordinates gives "
                + "det(gram) = -L*M + Xi. This is an algebraic identity over the reals; "
                + "it does not assert a global CFMP realization or a maximal stability ball."),
            Node("determinant-negative-iff",
                "Strict determinant criterion",
                "determinant_negative_iff",
                StatementCriterion(),
                "The determinant is negative exactly when the asymmetry remainder is "
                + "strictly smaller than the product L*M. The geometric interpretation "
                + "still requires the separate positive-length and realization hypotheses "
                + "of the surrounding theory."))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(F.Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);

    private static Formula StatementIdentity()
    {
        var r = F.Id("r"); var o = F.Id("o"); var A = F.Id("A");
        var B = F.Id("B"); var xi = F.Id("xi"); var zeta = F.Id("zeta");
        var args = new[] { r, o, A, B, xi, zeta };
        var det = Call("det", Call("gram", args));
        var rhs = F.Seq(Minus, Sp, Call("L", r, o, A, B), Sp, Times, Sp,
            Call("M", r, o, A, B), Sp, Plus, Sp, Call("Xi", args));
        return Eq(det, rhs);
    }

    private static Formula StatementCriterion()
    {
        var r = F.Id("r"); var o = F.Id("o"); var A = F.Id("A");
        var B = F.Id("B"); var xi = F.Id("xi"); var zeta = F.Id("zeta");
        var args = new[] { r, o, A, B, xi, zeta };
        return Iff(
            Lt(Call("det", Call("gram", args)), D(0)),
            Lt(Call("Xi", args), Mul(Call("L", r, o, A, B), Call("M", r, o, A, B))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Iff(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
}
