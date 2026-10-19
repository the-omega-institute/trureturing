using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.CriticalPoints;

internal sealed class RankOneTraceBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unitary rank-one trace and scalar analytic certificates for the spectral moment argument.",
        H("Trace bounds, interpolation and phase rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rank-one-trace-bound"),
                DeclarationHandle.Create("D5/S3/Zeros/CriticalPoints/RankOneTraceBound.norm_trace_rank_one_sum_le"),
                H("The unitary trace estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For finite complex Euclidean vectors r_j, nonnegative real weights a_j, unit complex phases gamma_j and a unitary matrix V, the norm of Tr(V sum_j a_j gamma_j r_j r_j*) is at most sum_j a_j times the squared norm of r_j. The estimate includes zero weights and zero vectors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rank-one-trace-phase-rigidity"),
                DeclarationHandle.Create("D5/S3/Zeros/CriticalPoints/RankOneTraceBound.phases_eq_of_norm_trace_rank_one_sum_eq"),
                H("Equality forces a common phase"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume the weights are strictly positive and every pairwise inner product of the r_j is nonzero. If the unitary trace estimate is an equality, then gamma_i=gamma_j for every i,j. Cauchy–Schwarz equality places each r_j in a unitary eigenspace; nonorthogonality identifies those eigenphases, and equality in the finite triangle inequality identifies the original phases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("schur-strip-moment-bound"),
                DeclarationHandle.Create("D5/S3/Zeros/CriticalPoints/RankOneTraceBound.strip_moment_bound_and_equality"),
                H("The interpolation bound and equality boundary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let M>0. A complex function continuous on the closed strip and differentiable in its interior, bounded there, with left boundary norm at most one and right boundary norm at most M, has norm at most M^(Re z) throughout the strip. If equality occurs at a real interior point theta with 0<theta<1, then the norm equals M at every right boundary point 1+iy. The equality argument applies the maximum modulus principle to exp(−z log M) times the function."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("schur-rotating-phase-injective"),
                DeclarationHandle.Create("D5/S3/Zeros/CriticalPoints/RankOneTraceBound.rotating_phase_injective"),
                H("Rotating phases determine their frequencies"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For complex u,v with u nonzero and real a,b, if u exp(iya)=v exp(iyb) for every real y, then u=v and a=b. Evaluation at zero determines the phase, and equality of derivatives at zero determines the frequency."))),
                DescribeRole.Theorem))));
}
