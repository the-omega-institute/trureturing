using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfQubitCoupledCubicDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfQubitCoupledCubic";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex Hermitian qubit endpoint coupling and the full pure cubic estimate.",
        H("Coupled two dimensional cubic trace estimate"),
        Blocks(
            Entry("hermitian", "Hermitian coordinates",
                "The two by two matrix with real diagonal a,b and upper off-diagonal z; "
                + "the lower off-diagonal is the complex conjugate of z.", DescribeRole.Definition),
            Entry("hermitian_isHermitian", "Hermitian coordinate construction",
                "The coordinate matrix is Hermitian for every pair of real diagonal "
                + "entries and every complex off-diagonal entry.", DescribeRole.Theorem),
            Entry("hermitian_eq", "All Hermitian qubit matrices",
                "Every complex Hermitian two by two matrix equals the coordinate "
                + "matrix formed from its two real diagonal entries and its upper entry.",
                DescribeRole.Theorem),
            Entry("weightedImage", "A symmetric two point kernel",
                "For real a,b,m, weightedImage multiplies K00 by a, K11 by b, "
                + "and both off-diagonal entries by m.", DescribeRole.Definition),
            Entry("endpoint_coupling", "The joint endpoint estimate",
                "For nonnegative a,b, let X-H with diagonal a-h,b-k and upper entry -z "
                + "and I+K with diagonal 1+r,1+s and upper entry w both be PSD. Then "
                + "|z|+sqrt(ab)|w| is at most sqrt((a-h+a(1+r))(b-k+b(1+s))). "
                + "The PSD determinant bounds and the two term Cauchy inequality "
                + "retain the original coupling; no inverse or strict endpoint is needed.",
                DescribeRole.Theorem),
            Entry("contraction_row", "The contraction row estimate",
                "For every complex Hermitian two by two K with both I+K and I-K PSD, "
                + "the squared modulus of K01 is at most 1-K00^2. Both determinant "
                + "constraints are used, and singular endpoints are allowed.", DescribeRole.Theorem),
            Entry("displacement_coupling", "The actual displacement entry",
                "If m>=sqrt(ab), the same coupled endpoints give "
                + "|z-mw|<=sqrt((2a-(h-ar))(2b-(k-bs)))+(m-sqrt(ab))|w|. "
                + "The argument uses the complex triangle inequality and the joint "
                + "endpoint estimate, with arbitrary complex phases.", DescribeRole.Theorem),
            Entry("displacement_row", "The weighted row estimate",
                "For a>0, h<=a and the two contraction endpoints of K, "
                + "|K01|^2<=2(2a-(h-aK00))/a. This also covers K01=0.",
                DescribeRole.Theorem),
            Entry("trace_weighted_square", "Exact weighted quadratic trace",
                "For the diagonal matrix X=diag(a,b) and Hermitian L with diagonal "
                + "u,v and upper entry z, Re Tr(XL^2)=a(u^2+|z|^2)+b(v^2+|z|^2). "
                + "All variables are arbitrary, and no positivity is assumed.",
                DescribeRole.Theorem),
            Paragraph(Text("These estimates are suppliers for the alpha=3, Y=I "
                + "two dimensional restriction of the He-Saunderson-Fawzi compatibility "
                + "question, arXiv:2502.05627v1 Conjecture 6.2 and the published "
                + "Conjecture 1, DOI 10.1007/s10107-025-02314-0. They do not prove "
                + "the unrestricted HSF conjecture or assert literature priority.")))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hsf-qubit-coupled-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
