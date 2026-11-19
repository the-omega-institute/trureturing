using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class DigitCapPowerGFDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/DigitCapPowerGF.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The bounded-digit counts with cap ell^r−1 have generating function "
            + "∏_{j<r} (1−z^(ell^j))^(−1).",
        H("Generating function of the counts with digit cap ell^r−1"),
        Blocks(
            Node("gf", "The generating function", "gf",
                "gf ell r is the integer power series whose n-th coefficient is "
                + "count (ell^r−1) ell n.", DescribeRole.Definition),
            Node("den", "The finite product", "den",
                "den ell r is the product of 1−z^(ell^j) over 0≤j<r.", DescribeRole.Definition),
            Node("product", "The product formula", "den_mul_gf",
                "For ell≥2 and every r, den ell r·gf ell r=1, so the generating function of "
                + "count (ell^r−1) ell n is ∏_{j<r}(1−z^(ell^j))^(−1); the counts are the numbers "
                + "of partitions of n into the parts 1, ell, …, ell^(r−1). For r=0 only the "
                + "empty representation exists. For the step, the identity count(a·ell−1) at n "
                + "= ∑_{t≤⌊n/ell⌋} count(a−1) at t with a=ell^r gives, after differencing in n, "
                + "(1−z)·G_{r+1}(z)=G_r(z^ell), since ⌊n/ell⌋ increases exactly when ell divides "
                + "n. Also den ell (r+1)=(1−z)·den ell r evaluated at z^ell. Substituting z^ell "
                + "is a ring homomorphism of power series, so den·gf at r+1 is the substituted "
                + "den·gf at r, which is 1.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("digit-cap-power-gf-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
