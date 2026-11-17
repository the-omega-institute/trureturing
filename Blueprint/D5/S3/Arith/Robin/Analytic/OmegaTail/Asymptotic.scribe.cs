using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaTail;

internal sealed class AsymptoticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact exponential rate of the large distinct-prime tail.", H("The exact exponential rate of the large distinct-prime tail"), Blocks(
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Asymptotic.result"),
                H("The two-sided counting asymptotic"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("As x tends to positive infinity, log(tailCount(0,x))/scale(x) tends to C0, where C0 is the infimum of rate(0,s) over s>1. For s>1 on u>0, the density q(s,u)=a(s)^s/(a(s)^s+u^s) has mass one, logarithmic moment m(s), and integrated binary entropy H(s). Moving s to the right of the unique saddle makes the moment strictly negative. Compact truncation and horizontal rescaling preserve mass one and give strict logarithmic slack; finite averaging increases entropy. The lower exponent follows from actual prime subsets, and continuity lets s decrease to the saddle. The phase-one upper_bound is applied directly at that saddle. The saddle lies strictly between one and two, C0=rate(0,saddle)=H(saddle), and C0>1. The eventual lower bound log(tailCount(0,x))/scale(x)>=C0-1/2>0 excludes tailCount(0,x)=0, so the count is eventually positive and its logarithm is meaningful. This concerns distinct prime factors. It supplies an upper-bound interpretation for Robin exceptions through the source necessary condition, and does not identify their own asymptotic count. The decimal interval 2.8054<C0<2.8055 is not certified by this theorem."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("luca-pomerance-sole-2025-large-omega-count-rate"), ResolutionKind.Proved)))));
}
