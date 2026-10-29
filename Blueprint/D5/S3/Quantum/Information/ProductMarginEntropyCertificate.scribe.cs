using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;
internal sealed class ProductMarginEntropyCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform high-reliability entropy certificate", H("ProductMarginEntropyCertificate"), Blocks(
            Describe.Lean(DescribeId.Create("binary-entropy-certificate"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ProductMarginEntropyCertificate.binary_entropy_certificate"),
                H("A uniform high-reliability entropy certificate"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("For every s in the closed interval [2/3,1], the binary-entropy expression in the statement is bounded below by (1-s)/(2s) times log(4096/3125). The proof applies binary entropy concavity to b=(1-s)/2 and b/(1-b), and then uses monotonicity up to 1/5. The endpoints use the actual continuous binary entropy values; no logarithm of a zero probability is differentiated."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("information-budget"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ProductMarginEntropyCertificate.information_budget_nonneg"),
                H("Combining the three information estimates"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("The two independent reliabilities a and b range over the entire unit interval. The conclusion combines a common trace bound with the two cross-contraction bounds and the classical absolute information bound. At a or b equal to zero, nonnegativity forces j=0. Otherwise reciprocal reliabilities split the proof into the low and high cases. This is a sufficient scalar budget: a quantum application must derive every input bound from its actual state and entropy; this statement alone does not assert that application."))), DescribeRole.Theorem))));
}
