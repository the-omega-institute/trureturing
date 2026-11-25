using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class ExactQubitBathErasureDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Decoherence/ExactQubitBathErasure.";
    private static LibraryNoteRef Bravyi =>
        LibraryNoteRef.Create("D5/L/Entropy/bravyi2004compatibility");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact feasibility and sharp bath heat for reset with a retained qubit record marginal.",
        H("Exact erasure with a Gibbs qubit bath"),
        Blocks(
            Describe.Lean(DescribeId.Create("qubit-bath-marginal-bound"),
                DeclarationHandle.Create(Module + "trace_mul_local_projections_le_three"),
                H("Rank-two projection bound for the two marginals"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Bravyi),
                Blocks(Paragraph(Text("The trace pairing of a rank-two projection with the sum of two lifted local rank-one projections is at most three. The finite calculation follows from the eigenvalues 2, 1, 1 and 0 of that sum. It gives the marginal-bias inequality for the repeated spectrum used in the erasure result."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("retained-record-qubit-gibbs-erasure"),
                DeclarationHandle.Create(Module + "gibbs_erasure_threshold_and_minimum"),
                H("Exact Gibbs-bath feasibility and minimum heat"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Bravyi),
                Blocks(
                    Paragraph(Text("A fair bit is recorded by two normalized pure qubit states of absolute overlap s. The independent Gibbs qubit bath has energy gap Δ and bias r=tanh(βΔ/2). A single unitary erases the bit to the prescribed pure state while retaining the average record marginal precisely when s is at most r. The operation permits correlations between the record and bath.")),
                    Paragraph(Text("Every admissible erasure increases the bath energy by at least Δs/2. The explicit attaining unitary leaves the bath diagonal with bias r−s. Heat is the increase in the expectation of the specified bath Hamiltonian."))),
                DescribeRole.Theorem))));
}
