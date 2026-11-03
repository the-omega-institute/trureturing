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
            Paragraph(Text("Application to the original Gram matrix. In the original edge order (12,13,14,34,24,23), write the six independent coordinates as (r,a,b,o,c,d), and set A=(a+c)/2, B=(b+d)/2, xi=(a-c)/2, zeta=(b-d)/2. Let U have columns (e0+e1)/sqrt(2), (e2+e3)/sqrt(2), (e0-e1)/sqrt(2), and (e2-e3)/sqrt(2). Both U-transpose*U and U*U-transpose are identity, and U-transpose*G*U is precisely gram(r,o,A,B,xi,zeta). Thus determinant_remainder_identity applies to the original G with these actual halfsum and halfdifference coordinates.")),
            Paragraph(Text("At xi=zeta=0, the first and last two coordinate blocks have determinants -L and M, and both cross blocks vanish. For the V4 center r=o, the orthogonal matrix with columns (1,1,1,1)/2, (1,1,-1,-1)/2, (1,-1,1,-1)/2, and (1,-1,-1,1)/2 diagonalizes the original G(r,A,B,r,A,B), in this order, with eigenvalues 1-r-A-B, 1-r+A+B, 1+r-A+B, and 1+r+A-B. The original determinant and the character determinant therefore retain the same sign; the basis change does not impose pairing symmetry on the six independent input coordinates.")),
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
