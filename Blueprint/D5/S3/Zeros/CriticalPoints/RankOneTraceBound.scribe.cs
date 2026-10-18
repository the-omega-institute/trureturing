using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.CriticalPoints;

internal sealed class RankOneTraceBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/CriticalPoints/RankOneTraceBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sharp unitary trace estimate for rank-one sums and its common-phase equality condition.",
        H("Rank-one trace bounds and phase rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rank-one-trace-bound"),
                DeclarationHandle.Create(Prefix + "Matrix.norm_trace_rank_one_sum_le"),
                H("The unitary trace estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite complex Euclidean vectors r_j, nonnegative real weights a_j, unit complex phases gamma_j and a unitary matrix V, the norm of Tr(V sum_j a_j gamma_j r_j r_j*) is at most sum_j a_j times the squared norm of r_j. The estimate includes zero weights and zero vectors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rank-one-trace-phase-rigidity"),
                DeclarationHandle.Create(Prefix + "Matrix.phases_eq_of_norm_trace_rank_one_sum_eq"),
                H("Equality forces a common phase"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume the weights are strictly positive and every pairwise inner product of the r_j is nonzero. If the unitary trace estimate is an equality, then gamma_i=gamma_j for every i,j. Cauchy–Schwarz equality places each r_j in a unitary eigenspace; nonorthogonality identifies those eigenphases, and equality in the finite triangle inequality identifies the original phases."))),
                DescribeRole.Theorem))));
}
