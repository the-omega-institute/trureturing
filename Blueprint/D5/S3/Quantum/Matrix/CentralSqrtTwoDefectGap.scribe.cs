using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CentralSqrtTwoDefectGapDocument : IScribeDocumentDefinition
{
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Eigenstructure/childs2003gluedtrees");

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
                "Let e_q be the fixed coordinate vector at q. If A is real symmetric, "
                + "B=A+c e_q e_q^T, and u,v are arbitrary vectors satisfying "
                + "Au=lambda u and Bv=mu v, then (mu-lambda)<u,v> "
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
            Entry("sectorSpectrum", "Complete reflection-sector spectrum",
                "sectorSpectrum(n) joins the two Hermitian eigenvalue enumerations of the "
                + "n+1 dimensional sectors. The sum type retains every index and every "
                + "algebraic multiplicity.", DescribeRole.Definition),
            Entry("sector_spectral_gap", "All-pair sector-union gap",
                "Any two distinct indices in the complete sector union have eigenvalue "
                + "distance at least [2*sqrt(2)/(1+sqrt(2))^2]/(n+1)^3. Positive-index "
                + "monotonicity and rank-one subadditivity constrain each threshold count "
                + "difference to zero or one. Two same-sector indices closer than the "
                + "cross-sector bound would force a count difference of at least two.", DescribeRole.Theorem),
            Entry("central_spectral_gap", "Actual full-matrix algebraic gap",
                "For every enumeration of all characteristic roots of centralDefect(n+1), "
                + "distinct indices have distance at least [2*sqrt(2)/(1+sqrt(2))^2]/(n+1)^3. "
                + "Folding the path at the defect gives two identical free-path blocks "
                + "coupled at their endpoints. The sum and difference bases conjugate "
                + "this matrix to the two Robin sectors. Characteristic-polynomial "
                + "factorization identifies the whole algebraic root multiset with the "
                + "sector union; injectivity follows from the quantitative gap.", DescribeRole.Theorem),
            Entry("uniform_inverse_cubic_gap", "Uniform gap of the fixed defect family",
                "There are c>0 and N>=1 such that for every n>=N the actual defect matrix "
                + "is Hermitian and every algebraic eigenvalue enumeration satisfies "
                + "|lambda(i)-lambda(j)|>=c/n^3 at distinct indices. One may take "
                + "c=2*sqrt(2)/(1+sqrt(2))^2 and N=1. The Fin(2*n-1+1) index type has "
                + "exactly 2*n elements under n>=1.", DescribeRole.Theorem),
            Paragraph(Text("The fixed matrix family and spectral-separation question are from "
                + "Childs et al., Exponential algorithmic speedup by a quantum walk, "
                + "arXiv:quant-ph/0209131v2, Section III.4, Lemma 2. The endpoint proof "
                + "uses every real energy and requires no asymptotic root enumeration. "
                + "The spectral conclusion supplies no physical access model, EXIT "
                + "algorithm, classical oracle lower bound or complete quantum/classical "
                + "separation.")))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("central-sqrt-two-defect-gap-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
