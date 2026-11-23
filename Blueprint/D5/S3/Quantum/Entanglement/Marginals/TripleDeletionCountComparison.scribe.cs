using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class TripleDeletionCountComparisonDocument : IScribeDocumentDefinition
{
    private const string Comparison =
        "D5/S3/Quantum/Entanglement/Marginals/TripleDeletionCountComparison.triple_kernel_exact";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compare the one-site deletion kernel with the allowed word space for a ban on triples.",
        H("Deletion kernel and allowed words when three consecutive occupations are forbidden"),
        Blocks(Describe.Lean(
            DescribeId.Create("triple-deletion-count-comparison"),
            DeclarationHandle.Create(Comparison),
            H("Exact comparison"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "On an open chain of k plus three sites, allow the binary words with no "
                    + "three consecutive ones. Write T for the Tribonacci sequence with initial "
                    + "values 0, 1 and 1. The allowed Hilbert space has dimension T(k+5). "
                    + "The supported complex matrix kernel of all single-site deletion traces "
                    + "has dimension 4 times the sum of T(k+3) and T(k+2). "
                    + "The kernel dimension is strictly less than twice the word count.")),
                Paragraph(Text(
                    "Each triple window must have a zero. This condition is preserved by "
                    + "taking the tail, and with the first window checked it implies "
                    + "Tribonacci admissibility by induction. The known count of Tribonacci "
                    + "names therefore gives the word count. The shifted Tribonacci sum "
                    + "satisfies the kernel recurrence and agrees at the first three lengths. "
                    + "The two recurrences at indices k+4 and k+5 and the positivity of "
                    + "T(k+1) give the strict inequality."))),
            DescribeRole.Theorem))));
}
