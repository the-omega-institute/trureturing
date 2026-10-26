using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution;

internal sealed class CriticalRenewalPathsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stopped exit estimates and consecutive-bit execution on the same history.",
        H("Critical renewal stopped paths and exact paid clock"),
        Blocks(
            Paragraph(Text("An adapted score path and its conditional moments give finite stopped drift, termination and exponential wrong-exit estimates under two probability laws. On a counted renewal table, the consecutive-bit execution realizes a stopped prefix of the same duration-mark blocks with an exact paid clock.")),
            Describe.Lean(
                DescribeId.Create("critical-renewal-exit-time"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths.exitTime"),
                H("First completed-block exit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every measurable carrier Omega, real process S indexed by natural numbers, and real threshold b, exitTime(S,b) is Mathlib hittingAfter(S,{x:b<=|x|},1). It takes values in WithTop Nat and equals infinity if no positive block index reaches the threshold. Index zero is excluded."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("critical-renewal-capped-time"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths.cappedTime"),
                H("Finite truncation of the block clock"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every Omega, S, b, natural n and sample omega, cappedTime(S,b,n,omega) is the real cast of untopA(min(n,exitTime(S,b,omega))). The minimum is always finite, including paths whose exit time is infinity, so this value is exactly the number of completed blocks through the bounded stopping index."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("critical-renewal-finite-stopped-drift"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths.finite_stopped_drift"),
                H("Predictability, overshoot and finite drift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every probability measure mu on Omega, natural-time filtration F, strongly F-adapted real process S, and real b,d, assume b>0, S(0)=0 everywhere, |S(n+1)-S(n)|<=1 everywhere for every n, and E_mu[S(n+1)-S(n)|F(n)]=d almost surely for every n. With G=exitTime(S,b), the event {n<G} is F(n)-measurable for every n; equivalently {G>=n+1} is predictable before the next block. At every finite n and every sample, |S(min(n,G))|<=b+1. For every finite n, E_mu[S(min(n,G))]=d E_mu[min(n,G)]. Neither G finite nor E_mu[G] finite is assumed. The centered score is a martingale; its bounded stopped expectations give the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("critical-renewal-integrable-exit"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths.integrable_exit"),
                H("Finite drift proves termination before risk limits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under every hypothesis of finite_stopped_drift and additionally d>0, the nonnegative expectation of sup_n ofReal(min(n,G)) is at most ofReal((b+1)/d). The exit G is finite almost surely. Its real cast untopA(G) is integrable and has expectation at most (b+1)/d. Monotone convergence of the bounded clocks proves the nonnegative expectation bound first; finite expectation then excludes infinite-exit paths. Only afterwards is untopA(G) used as the real exit count, with arbitrary values on its null exceptional set."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("critical-renewal-stopping-risks"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths.critical_renewal_stopping_risks"),
                H("One threshold and both proof orientations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let mu(false),mu(true) be any two probability laws on the same measurable carrier and S one strongly F-adapted score path. Assume S(0)=0 and all increments have absolute value at most one everywhere. Fix positive D0,V0,I, alpha and delta with alpha<1/2 and delta<=1/2, and a real Delta satisfying D0 I<=Delta. Under law i, require the conditional increment mean to equal sigma(i) Delta/2 and the conditional second moment to be at most V0 I, at every block. Here sigma(false)=-1 and sigma(true)=1 are proof signs.")),
                    Paragraph(Text("Set lambda=min(1,D0/(2 exp(1) V0)), A=log(1/alpha)/lambda, H=ceil(A/delta) using the integer ceiling, b=H delta, and G=exitTime(S,b). These are the original constants; positivity and A<=b<=A+1/2 are derived. For every finite n and sample, |S(min(n,G))|<=b+1<=A+3/2. Under each law i, {n<G} is F(n)-measurable and E_i[sigma(i) S(min(n,G))]=(Delta/2) E_i[min(n,G)]. The same G is finite almost surely under each law, its real cast is integrable, and E_i G<=2(A+3/2)/Delta.")),
                    Paragraph(Text("For each i, every finite stopped exponential exp(-lambda sigma(i) S(min(n,G))) has expectation at most one, and the limiting exp(-lambda sigma(i) S(G)) has expectation at most one. The wrong-exit event {sigma(i) S(G)<=-b} has probability at most exp(-lambda b)<=alpha. For i=false this is the upper exit S(G)>=b; for i=true it is the lower exit S(G)<=-b. Both statements use one score path and threshold; no sign is an input to the controller.")),
                    Paragraph(Text("The one-step estimate uses exp(lambda u)<=1+lambda u+(exp(1)/2)lambda^2 u^2 for |u|<=1 and 0<=lambda<=1, derived from Mathlib's exponential remainder bound. Conditional first and second moments give the exponential supermartingale. The proof obtains finite G from the finite drift and monotone convergence before passing to the risk limit. The deterministic overshoot bound dominates the stopped exponentials for bounded convergence. Markov's integral inequality then bounds each wrong exit.")),
                    Paragraph(Text("For the actual source, I=s^(2r) J and delta=J/2^(rJ). The relevant filtration contains the initial wait and completed joint gap/coin blocks, and S is the literal table's completed-block evidence. The same-run realization below identifies emitted labels and paid stopping with the completed-gap exit. Conditional source moments and expected payment are separate probabilistic results."))),
                DescribeRole.Theorem),
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
