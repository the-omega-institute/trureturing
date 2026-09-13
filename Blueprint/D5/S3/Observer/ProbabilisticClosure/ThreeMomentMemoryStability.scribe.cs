using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class ThreeMomentMemoryStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kernel estimation stays stable near zero coupling even when coordinate inversion does not.",
        H("Coupling-Uniform Three-Moment Error Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-moment-memory-stability"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/ThreeMomentMemoryStability.three_moment_error_bound"),
                H("Every lag has an explicit absolute error bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let each of the actual response moments u, u^2+v^2 and "
                    + "u^3+2uv^2+v^2w be measured with error at most epsilon. The first "
                    + "two noisy readings are clipped into [-1,1]; the theorem states all "
                    + "true and observed bounds explicitly. Set ghat=rhat2-rhat1^2 and "
                    + "zhat=rhat3-2rhat1*rhat2+rhat1^3. Return zero for ghat<=0; otherwise "
                    + "return ghat*clip(zhat/ghat)^k. The coefficient error is at most "
                    + "(3+11*k)*epsilon at every natural lag k, without a lower bound "
                    + "on v^2. The live proof bounds the g error by 3*epsilon, the z "
                    + "error by 8*epsilon, and the coupling-weighted multiplier error "
                    + "by 11*epsilon before using the power-difference estimate. The "
                    + "small denominator cancels at the level of the target kernel. "
                    + "This is finite-horizon stability, not a uniform-in-time guarantee "
                    + "or recovery of the sign of the hidden coupling."))),
                DescribeRole.Theorem))));
}
