using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.CothBernoulliDegree;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/zhu2020completelymonotonicdegrees");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derivative signs of the power-weighted hyperbolic cotangent remainder.",
        H("The derivative sign theorem"), Blocks(
            Describe.Lean(DescribeId.Create("coth-bernoulli-degree-result"),
                DeclarationHandle.Create("D5/S3/Analytic/CothBernoulliDegree/Result.result"),
                H("The two derivative orders"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let m and n be natural numbers with m at least one and n at least two, and put M=m+2n. The signed remainder P has derivative of order M-2 strictly positive at every positive t. Its derivative of order M-1 fails to be strictly positive everywhere on the positive ray.")),
                    Paragraph(Text("The partial-fraction formula and its differentiated series express these derivatives as positive multiples of rational-kernel derivatives. At order M-2 each kernel is strictly positive. The derivative series is summable, so its sum is strictly positive.")),
                    Paragraph(Text("At t=5 pi/M, the derivative of order M-1 is at most -(M-1)!/(8 pi^(2n+1)). The first normalized summand is at most -1/8 by the phase and amplitude estimate. The remaining normalized summands are bounded above by a reciprocal-power tail of at most 1/16. Restoring the common positive factor gives the stated strictly negative value and hence the second clause."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhu-2020-coth-bernoulli-remainder-derivative-signs"),
                    ResolutionKind.Proved)))));
}
