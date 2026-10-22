using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.TaylorMajorization;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/TaylorMajorization/Defs";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered Taylor coefficients and spectral comparison.",
        H("Taylor coefficients and weak majorization"), Blocks(
            Paragraph(Text("For complex Hermitian matrices A and B, Q at order k is the sum of choose(k,p) times A to the p times B to the k-p over p from zero to k. Its Hermitian part R is (Q+Q*)/2. The claim compares every initial sum of the nonincreasing eigenvalues of (A+B) to the k with the corresponding sum for R, for every positive dimension and every k at least five. The defect is the real trace of R minus the real trace of (A+B) to the k.")),
            Describe.Lean(DescribeId.Create("taylor-majorization-r-hermitian"),
                DeclarationHandle.Create(Module + ".taylorR_isHermitian"),
                H("Hermitian Taylor coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Hermitian part R is Hermitian at every order, so its sorted real eigenvalues are defined."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("taylor-majorization-trace-reduction"),
                DeclarationHandle.Create(Module + ".weakMaj_trace"),
                H("The full spectral sum is the trace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Weak majorization of the nonincreasing real eigenvalues of Hermitian X and Y implies that the real trace of X is at most that of Y. Take the initial sum of length n and reindex the spectral trace identity along the equivalence used by the sorted eigenvalue API."))), DescribeRole.Theorem))));
}
