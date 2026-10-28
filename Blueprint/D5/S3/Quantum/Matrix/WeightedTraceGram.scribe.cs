using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class WeightedTraceGramDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/WeightedTraceGram";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted trace Gram positivity",
        H("Weighted trace Gram positivity"),
        Blocks(
            Entry("weighted_traceGram_nonneg", "PSD weighted trace form",
                "For arbitrary finite index types n and m, complex n by n PSD L,R, arbitrary matrix words q indexed by m, and a real m by m PSD coefficient matrix M, the sum of M_ij Re Tr(L (q_i)* R q_j) is nonnegative. The proof uses a real square root of M and PSD congruence. Singular weights and non-Hermitian words are included."))));
    private static DocumentBlock Entry(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("weightedtracegram-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
