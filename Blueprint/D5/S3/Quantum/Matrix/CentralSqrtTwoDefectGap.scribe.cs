using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CentralSqrtTwoDefectGapDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rank-one sector separation for the central square-root-two defect Jacobi family.",
        H("Central square-root-two defect gap"),
        Blocks(
            Entry("rank_one_gap_from_identity", "Inverse gap from endpoint control",
                "For real c,K,lambda,mu,x,y,z with c>0, K>0, (lambda-mu)z=cxy, "
                + "1<=K*x^2, 1<=K*y^2, and |z|<=1, one has c/K<=|lambda-mu|. "
                + "This is the quantitative inverse-cubic bridge once K is the endpoint "
                + "control constant.", DescribeRole.Theorem),
            Entry("rank_one_cross_identity", "Rank-one cross-sector identity",
                "If A is real symmetric, B=A+c vv^T with v the coordinate vector at q, "
                + "and Au=lambda u, Bv=mu v, then (mu-lambda)<u,v> "
                + "=c*u(q)*v(q). The identity is proved by the matrix update and symmetry.",
                DescribeRole.Theorem),
            Entry("rank_one_gap_of_matrices", "Rank-one cross-sector gap",
                "Combining the preceding identity with endpoint controls "
                + "1<=K*u(q)^2 and 1<=K*v(q)^2 and |<u,v>|<=1 gives "
                + "c/K<=|lambda-mu| for actual eigenpairs of the two symmetric matrices.",
                DescribeRole.Theorem),
            Entry("centralEdges", "Central square-root-two edge sequence",
                "For n>=1, centralEdges(n) is the edge sequence on Fin(2*n-1+1) whose "
                + "unique central entry at n-1 is sqrt(2), with every other entry 1; "
                + "the displayed dimension is 2*n under the stated threshold.",
                DescribeRole.Definition),
            Entry("centralDefect", "Actual central defect Jacobi matrix",
                "centralDefect(n) is the zero-diagonal Jacobi matrix of dimension 2*n-1+1 "
                + "with nearest-neighbour entries centralEdges(n), hence exactly the "
                + "fixed central-sqrt(2) defect matrix from the source event after the "
                + "threshold identification.",
                DescribeRole.Definition),
            Entry("recurrence_endpoint_observability", "Uniform endpoint observability",
                "Let n>=1 and y(0)=0. Suppose y(j+2)=t*y(j+1)-y(j) for j+2<=n+1 "
                + "and y(n+1)=b*y(n). Then the sum of y(j)^2 over 1<=j<=n is at most "
                + "(1+|b|)^2*n^3*y(n)^2. The estimate holds for every real t, including "
                + "both band edges and the exterior regimes. Inside |t|<=2, the finite "
                + "continuant formula and the Chebyshev bound |U_k(x)|<=k+1 control the "
                + "backward recurrence. Outside the band, the forward coordinate magnitudes "
                + "are nondecreasing.", DescribeRole.Theorem),
            Entry("sectorMatrix", "Concrete reflection sector",
                "sectorMatrix(n,b) is the unit-edge path on n+1 vertices, with diagonal "
                + "zero except for the last entry b.", DescribeRole.Definition),
            Entry("sector_endpoint_observability", "Sector eigenvector endpoint bound",
                "For every eigenpair sectorMatrix(n,b)*v=t*v, the sum of v(i)^2 is at "
                + "most (1+|b|)^2*(n+1)^3*v(n)^2. No normalization, nonzero endpoint, "
                + "band location or eigenvalue separation is assumed.", DescribeRole.Theorem),
            Entry("sector_inverse_cubic_gap", "Opposite-sector inverse-cubic gap",
                "For unit eigenvectors of sectorMatrix(n,-sqrt(2)) and sectorMatrix(n,sqrt(2)), "
                + "with eigenvalues lambda and mu, their distance is at least "
                + "[2*sqrt(2)/(1+sqrt(2))^2]/(n+1)^3. This bound is uniform over all "
                + "opposite-sector pairs, including exterior modes. It does not by itself "
                + "bound pairs belonging to the same sector.", DescribeRole.Theorem),
            Paragraph(Text("The full-matrix reflection identification, source quantization and "
                + "adjacent-sector alternation needed for the complete uniform inverse-cubic "
                + "event remain separate obligations. This module records the compiled "
                + "rank-one bridge, finite-recurrence endpoint estimate and fixed matrix family.")))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("central-sqrt-two-defect-gap-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
