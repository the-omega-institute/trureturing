using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class DelannoySquareRootsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/DelannoySquareRoots.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/maowang2026narayana");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original Delannoy paths yield the matrix-square divided difference and exclude its root-count threshold.",
        H("Original Delannoy Matrix Square"),
        Blocks(
            Paragraph(Text(
                "Mao and Wang, The Narayana transformation, arXiv:2607.01572v1, "
                + "Conjecture 4.1 asks for real nonpositive roots of A squared and "
                + "D squared. Only the original D squared clause is selected here. "
                + "The all-degree complex-root assertion remains unproved in this module.")),
            Paragraph(Text(
                "Step words use east, north and northeast. Their endpoint sums count "
                + "east and north with weight one and northeast with weight two. "
                + "The finite set paths(n) contains exactly the words ending at a point "
                + "whose coordinate sum is n. Filtering by the second coordinate k "
                + "therefore counts paths to (n-k,k), and there are no entries above "
                + "the diagonal. squareEntry(n,k) is the sum of D(n,j)D(j,k) over "
                + "k <= j <= n. squareRow(n) uses precisely these product coefficients.")),
            Describe.Lean(
                DescribeId.Create("delannoy-square-source-correspondence"),
                DeclarationHandle.Create(Prefix + "source_correspondence"),
                H("Path Correspondence, Divided Difference and Endpoint Exclusion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The disjoint east, north and northeast path images give the "
                        + "ordinary-row recurrence T_(n+2)=(1+x)T_(n+1)+xT_n. "
                        + "Coefficient extraction yields column k as g f^k, with "
                        + "g=1/(1-t) and f=t(1+t)/(1-t). The actual matrix-square "
                        + "sum then gives F=g times T(f). Formal substitution proves "
                        + "[(1-t)(1-2t-t²)-xt(1+t)(1+t²)]F=1-t in the power-series "
                        + "ring with integer polynomial coefficients. This proves the "
                        + "source correspondence from actual paths rather than assuming "
                        + "a recurrence-only representation.")),
                    Paragraph(Text(
                        "For every n, T_n(1-sqrt(2)) is nonzero. Evaluate T_n first "
                        + "in the integer quadratic ring at 1-sqrt(2). Mathlib's "
                        + "injective real embedding shows that a zero there would "
                        + "be a zero element of that ring. The conjugate embedding "
                        + "would then give T_n(1+sqrt(2))=0. Its actual recurrence "
                        + "has positive initial values and positive weights at "
                        + "1+sqrt(2), so that evaluation is strictly positive. "
                        + "The quadratic-ring embedding and polynomial homomorphism "
                        + "laws are reused from pinned Mathlib.")),
                    Paragraph(Text(
                        "For nonzero complex u and v with u+v+uv=1 and yuv=1, "
                        + "the theorem proves y(v-u)(-1)^n G_n(-y) "
                        + "= T_n(-u)/u^(n+1)-T_n(-v)/v^(n+1) for every n. "
                        + "The series whose coefficients are T_n(-u)/u^(n+1) "
                        + "is the reciprocal of q_u=t²+(u-1)t+u. The transformed "
                        + "source denominator factors as y q_u q_v. Subtracting "
                        + "the two reciprocal series and extracting coefficients "
                        + "gives the original squared-row identity. Its multiplied "
                        + "form permits u=v; division by v-u requires distinctness."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For P_n(y)=(-1)^n G_n(-y), the formal bridge factors the source "
                + "denominator into two quadratics indexed by u and "
                + "v=(1-u)/(1+u), where y=1/(uv). A divided difference connects "
                + "P_n to the ordinary rows. Upper-circle phase crossings and "
                + "disjoint real Chebyshev sign intervals must supply the complementary "
                + "root counts. Those counts and degree closure are "
                + "unformalized obligations. No simplicity, interlacing, higher-power "
                + "or Eulerian claim follows from the source bridge.")))));
}
