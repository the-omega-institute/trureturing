using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class CorrelationMinorNormSpectralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual native singular-value and nuclear tail correspondences", H("Actual native singular-value and nuclear tail correspondences"), Blocks(
            Entry("gram-to-euclidean-lin", "gram_toEuclideanLin", "gram toEuclideanLin",
                "The actual real column Gram matrix acts as the adjoint composite of the Euclidean linear map of the original rectangular matrix.", DescribeRole.Theorem),
            Entry("native-singular-value", "native_singular_value", "native singular value",
                "For every real rectangular matrix, its native descending zero-extended singular values are exactly the square roots of the sorted column-Gram eigenvalues, with explicit finite index correspondence.", DescribeRole.Theorem),
            Entry("trace-norm-eq-native-sum", "traceNorm_eq_native_sum", "traceNorm eq native sum",
                "The existing actual real rectangular CFC trace norm equals the complete native descending singular-value sum through the column dimension, retaining zero values.", DescribeRole.Theorem),
            Entry("op-norm-eq-native-first", "opNorm_eq_native_first", "opNorm eq native first",
                "The actual induced Euclidean matrix operator norm equals the first native descending singular value. Zero maps and empty dimensions are included.", DescribeRole.Theorem),
            Entry("trace-norm-sub-rank-one-tail", "traceNorm_sub_rankOne_tail", "traceNorm sub rankOne tail",
                "For every real rectangular A and arbitrary actual Euclidean a,b, traceNorm(A)-operatorNorm(A) is at most traceNorm(A-ab transpose). An actual contractive projected dual witness proves this; zero a or b and rank deficiency remain included.", DescribeRole.Theorem),
            Entry("native-tail-le-centered", "native_tail_le_centered", "native tail le centered",
                "For every retained length 1≤k≤n, the actual descending native singular-value tail from index one through k-1 is at most the actual CFC trace norm after subtracting ab transpose. Index one corresponds to the source one-based second singular value. This supplier is consumed by the actual marginal/purity theorem in CorrelationMinorNormCovariance.", DescribeRole.Theorem),
            Entry("trace-norm-transpose", "traceNorm_transpose", "traceNorm transpose",
                "Transposition preserves the existing real rectangular CFC nuclear norm. The proof uses its actual attained contractive duality, including zero and rectangular cases.", DescribeRole.Theorem),
            Entry("native-tail-eq-trace-norm-sub", "native_tail_eq_traceNorm_sub", "native tail eq traceNorm sub",
                "For positive finite row and column dimensions, the actual descending tail through the smaller dimension equals the CFC nuclear norm minus the Euclidean operator norm. All additional ambient singular values are proved zero by range dimension, rather than discarded by convention.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/peledteenicarmicohen2021minor")),
            Blocks(Paragraph(Text(text))), role);
}
