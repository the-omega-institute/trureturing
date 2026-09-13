using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class FiniteHorizonMemoryStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite response errors propagate through causal memory inversion with an explicit bound.",
        H("Finite-Horizon Memory Reconstruction Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-horizon-memory-error"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/FiniteHorizonMemoryStability.finite_horizon_error_bound"),
                H("Responses through H+2 control kernels through H"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In a normed, possibly noncommutative ring, reconstruct the kernel by "
                    + "R(n+2)-R(1)R(n+1) minus the sum of already reconstructed kernels "
                    + "times earlier responses. Assume the exact pair R,M satisfies the "
                    + "block-elimination recurrence; the true and observed responses and "
                    + "true kernels have norm at most one on the stated finite ranges. "
                    + "If response errors through H+2 are at most epsilon, then the "
                    + "kernel error at every n<=H is at most (2^(n+2)-1)*epsilon. "
                    + "Strong induction uses the actual ordered product error inequality "
                    + "and a finite geometric sum. No hidden-system inversion or singular "
                    + "value lower bound is assumed. Isotypic matrix-element sampling "
                    + "and radial normalization are explained in the appended theory; "
                    + "this declaration does not itself construct a group decomposition "
                    + "or certify a physical process. The exact recurrence premise is "
                    + "discharged by the existing causal-recovery result when applied "
                    + "to an actual block dynamics."))),
                DescribeRole.Theorem))));
}
