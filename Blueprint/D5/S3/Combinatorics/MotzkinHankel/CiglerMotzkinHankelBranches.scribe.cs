using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MotzkinHankel;

internal sealed class CiglerMotzkinHankelBranchesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelBranches.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2022motzkin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct reciprocal roots give two formal branches, and coefficients of integral unit powers are polynomial in the exponent.",
        H("Formal Reciprocal Branches and Polynomial Exponents"),
        Blocks(
            Node("cigler-motzkin-hankel-branches-formal", "The two reciprocal formal branches", "formal_branches",
                "Let K be a field, let phi be a ring homomorphism from the integer polynomial ring in t and s to K, and let alpha be nonzero with alpha - alpha inverse nonzero and phi(t) = alpha + alpha inverse. There is a formal power series z(y) with constant coefficient alpha and z + z inverse = phi(t) - y. The constant coefficient of z - z inverse is nonzero. Among series with constant coefficient alpha, z is the unique solution of w squared - (phi(t) - y)w + 1 = 0. Put a = (phi(s) - y - z inverse)/(z - z inverse) and b = (z - phi(s) + y)/(z - z inverse). For every nonnegative integer r, (-1)^r p_r(y) after applying phi to its coefficients equals a z^r + b(z inverse)^r, while (-1)^(r+1) b_r(y) after the same coefficient map equals a(z inverse)^(r+1) + b z^(r+1). All these identities are formal power series identities over K.", DescribeRole.Theorem),
            Node("cigler-motzkin-hankel-branches-unit-coefficients", "Polynomial dependence on an integral exponent", "unit_power_coefficients",
                "Let K be a field of characteristic zero, let u be an invertible formal power series with constant coefficient one, let H be any formal power series over K, and let h be a nonnegative integer. There is a polynomial P over K of natural degree at most h such that, for every integer n, P evaluated at n equals the coefficient of y^h in H(y)u(y)^n. The statement includes negative exponents, interpreted using the inverse of u.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
