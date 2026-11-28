using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.LocalCompression;

internal sealed class PetzErasureGramBoundDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The squared joint and marginal roots control the orthogonal population of the ordinary Petz benchmark.",
        H("Gram bound for complete erasure"),
        Blocks(
            Paragraph(Text(
                "For a rank-one retained likelihood, the ordinary Petz benchmark uses the first "
                + "column of the joint square root. Its component orthogonal to the corresponding "
                + "marginal column is measured by the Gram numerator below.")),
            Entry("squared-root-block-traces", "traceBlocks_root_mul", "Block traces of the squared joint root",
                "The diagonal partial traces are Hilbert–Schmidt norm squares. "
                + "The lower off-diagonal trace is Tr((A + C)B)."),
            Entry("hilbert-space-bound", "gram_bound", "Hilbert-space Gram estimate",
                "The diagonal norm identities and the off-diagonal pairing bound the residual "
                + "by (a² + ac)δ in squared norm."),
            Entry("matrix-gram-bound", "matrix_gram_bound", "Gram bound with the actual partial trace",
                "When the partial trace of the squared joint root equals the square of the qubit root, "
                + "the defect δ = ‖B‖² − |b|² is nonnegative and ‖aB − bA‖² ≤ (a² + ac)δ."),
            Entry("orthogonal-population", "benchmark_orthogonal_numerator", "Orthogonal population from the benchmark Gram",
                "Evaluating the Gram of the first joint-root block column on (−conj b, a) "
                + "gives the numerator ‖aB − bA‖²."),
            Entry("least-quadratic-coefficient", "quadratic_coefficient_isLeast", "Sharp quadratic coefficient",
                "The least coefficient relative to a² + c² on the nonnegative quadrant is (1 + √2)/2."))));

    private static DocumentBlock Entry(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
