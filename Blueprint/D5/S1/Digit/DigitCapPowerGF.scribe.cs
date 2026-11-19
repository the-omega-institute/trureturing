using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class DigitCapPowerGFDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/DigitCapPowerGF.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/coons2026calkinwilf");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The bounded-digit counts with cap ell^r−1 have generating function "
            + "∏_{j<r} (1−z^(ell^j))^(−1) and grow like n^(r−1).",
        H("Generating function of the counts with digit cap ell^r−1"),
        Blocks(
            Node("gf", "The generating function", "gf",
                "gf ell r is the integer power series whose n-th coefficient is "
                + "count (ell^r−1) ell n.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("den", "The finite product", "den",
                "den ell r is the product of 1−z^(ell^j) over 0≤j<r.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("product", "The product formula", "den_mul_gf",
                "For ell≥2 and every r, den ell r·gf ell r=1, so the generating function of "
                + "count (ell^r−1) ell n is ∏_{j<r}(1−z^(ell^j))^(−1); the counts are the numbers "
                + "of partitions of n into the parts 1, ell, …, ell^(r−1). For r=0 only the "
                + "empty representation exists. For the step, the identity count(a·ell−1) at n "
                + "= ∑_{t≤⌊n/ell⌋} count(a−1) at t with a=ell^r gives, after differencing in n, "
                + "(1−z)·G_{r+1}(z)=G_r(z^ell), since ⌊n/ell⌋ increases exactly when ell divides "
                + "n. Also den ell (r+1)=(1−z)·den ell r evaluated at z^ell. Substituting z^ell "
                + "is a ring homomorphism of power series, so den·gf at r+1 is the substituted "
                + "den·gf at r, which is 1. The product formula is displayed in the proof of "
                + "Theorem 2 of M. Coons (arXiv:2611.08109).", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source)),
            Node("bounds", "Explicit growth bounds", "count_bounds",
                "For ell≥2, every r and every n, C(⌊n/ell^r⌋+r, r) ≤ count (ell^(r+1)−1) ell n ≤ "
                + "(n+1)^r. Both follow by induction on r from the summation identity, starting "
                + "from count (ell−1) ell n=1. For the upper bound each of the ⌊n/ell⌋+1 summands "
                + "is at most (n+1)^r. For the lower bound the summands at t=s·ell^r with "
                + "s≤⌊n/ell^(r+1)⌋ already give the hockey-stick sum of C(s+r, r), which is "
                + "C(⌊n/ell^(r+1)⌋+r+1, r+1).", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("theta", "Polynomial growth of order r", "count_isTheta",
                "For ell≥2 and every r, count (ell^(r+1)−1) ell n is Θ(n^r) as n→∞; with the "
                + "cap written as ell^r−1 the order is n^(r−1). The upper constant is 2^r for "
                + "n≥1, and the lower bound uses C(m+r, r) ≥ (m+1)^r/r! with m=⌊n/ell^r⌋ and "
                + "n ≤ ell^r(m+1). Coons's equation (4) gives the sharper asymptotic "
                + "n^(r−1)/(ell^(r(r−1)/2)(r−1)!) for cap ell^r−1.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source)))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("digit-cap-power-gf-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), provenance,
            Blocks(Paragraph(Text(prose))), role);
}
