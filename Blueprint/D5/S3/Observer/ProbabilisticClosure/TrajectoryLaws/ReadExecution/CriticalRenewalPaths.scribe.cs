using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution;

internal sealed class CriticalRenewalPathsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One uninterrupted actual history.",
        H("Critical renewal Paths"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("criticalrenewalpaths-consecutive-block-event"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths.consecutive_block_event"),
                H("One uninterrupted actual history"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let tau be any natural initial wait and let blocks be any sequence of finite zero-coin lists with closing-tick coins. Put clock(n)=tau+1+sum over h<n of (length(zeros(h))+1). For every n and k at most length(zeros(n)), event(clock(n)+k) is (zero, the kth zero coin) when k is smaller than that length, and (one, the block tick coin) at equality.")),
                    Paragraph(Text("event is zero throughout the initial wait and one at its closing tick. The clock is strictly increasing and unbounded, so every later read has one block address. These addresses and coin lists are analytical coordinates. The successor function receives only the current counted state, actual bit and fresh outcome."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("criticalrenewalpaths-stopped-prefix-payment"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths.stopped_prefix_payment"),
                H("Exact counted stopped-prefix payment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix positive H, natural J, immutable Tick J, a natural initial wait tau, a sequence of finite blocks and a natural g. Write E(n) for the sum of the first n block increments. Suppose E(g) lies outside the open interval (-H,H) and E(n) lies inside it for every n<g.")),
                    Paragraph(Text("Then the first gap threshold time gapStop equals g. The first paid label time paidStop equals exactly 1+tau+sum over n<g of (length(zeros(n))+1). At clock(g) the actual run equals target(E(g)), and at every strictly earlier bit prefix it is not a label. The emitted label is one if and only if E(g) is at least H, and zero if and only if E(g) is at most -H.")),
                    Paragraph(Text("For every n<g and k at most that block's zero count, the run at clock(n)+k is precisely evidence E(n) and the phase obtained from that same block's first k zero outcomes. For every nonzero real grid spacing delta and every n, E(n)=score(delta,n)/delta, where score is the ordinary real sum of the increments multiplied by delta. The same carrier has exact cardinality 3+(2H-1)(J+1).")),
                    Paragraph(Text("Every failed or holding interval, every dead suffix, the first wait, the first tick and the terminal closing tick is charged. There is no terminal partial interval and no stopping-time label decoder. Potential blocks after termination are an analytical continuation of the same history."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("criticalrenewalpaths-infinite-prefix"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths.infinite_prefix"),
                H("Infinite execution keeps its meaning"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive H and arbitrary J, Tick J, tau and block sequence, if every E(n) lies strictly between -H and H, both the completed-gap threshold time and the actual paid label time are infinite.")),
                    Paragraph(Text("No default label is assigned to an infinite history. Each individual gap is finite, and the growing clock exhausts all finite bit prefixes."))),
                DescribeRole.Theorem))));
}
