using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution;

internal sealed class CriticalRenewalPaymentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stopped drift, both exit risks and exact paid means.",
        H("Critical renewal stopped exit and payment"),
        Blocks(
            Paragraph(Text("An adapted score path and its conditional moments give finite stopped drift, termination and exponential wrong-exit estimates under two probability laws. For the actual renewal execution, predictable inclusion of completed gaps also gives an exact mean-payment identity on the same source law. Duration and score within one gap need not be independent.")),
            Describe.Lean(
                DescribeId.Create("critical-renewal-exit-time"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPayment.exitTime"),
                H("First completed-block exit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every measurable carrier Omega, real process S indexed by natural numbers, and real threshold b, exitTime(S,b) is Mathlib hittingAfter(S,{x:b<=|x|},1). It takes values in WithTop Nat and equals infinity if no positive block index reaches the threshold. Index zero is excluded."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("critical-renewal-capped-time"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPayment.cappedTime"),
                H("Finite truncation of the block clock"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every Omega, S, b, natural n and sample omega, cappedTime(S,b,n,omega) is the real cast of untopA(min(n,exitTime(S,b,omega))). The minimum is always finite, including paths whose exit time is infinity, so this value is exactly the number of completed blocks through the bounded stopping index."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("critical-renewal-finite-stopped-drift"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPayment.finite_stopped_drift"),
                H("Predictability, overshoot and finite drift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every probability measure mu on Omega, natural-time filtration F, strongly F-adapted real process S, and real b,d, assume b>0, S(0)=0 everywhere, |S(n+1)-S(n)|<=1 everywhere for every n, and E_mu[S(n+1)-S(n)|F(n)]=d almost surely for every n. With G=exitTime(S,b), the event {n<G} is F(n)-measurable for every n; equivalently {G>=n+1} is predictable before the next block. At every finite n and every sample, |S(min(n,G))|<=b+1. For every finite n, E_mu[S(min(n,G))]=d E_mu[min(n,G)]. Neither G finite nor E_mu[G] finite is assumed. The centered score is a martingale; its bounded stopped expectations give the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("critical-renewal-integrable-exit"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPayment.integrable_exit"),
                H("Finite drift proves termination before risk limits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under every hypothesis of finite_stopped_drift and additionally d>0, the nonnegative expectation of sup_n ofReal(min(n,G)) is at most ofReal((b+1)/d). The exit G is finite almost surely. Its real cast untopA(G) is integrable and has expectation at most (b+1)/d. Monotone convergence of the bounded clocks proves the nonnegative expectation bound first; finite expectation then excludes infinite-exit paths. Only afterwards is untopA(G) used as the real exit count, with arbitrary values on its null exceptional set."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("critical-renewal-stopping-risks"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPayment.critical_renewal_stopping_risks"),
                H("One threshold and both proof orientations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let mu(false),mu(true) be any two probability laws on the same measurable carrier and S one strongly F-adapted score path. Assume S(0)=0 and all increments have absolute value at most one everywhere. Fix positive D0,V0,I, alpha and delta with alpha<1/2 and delta<=1/2, and a real Delta satisfying D0 I<=Delta. Under law i, require the conditional increment mean to equal sigma(i) Delta/2 and the conditional second moment to be at most V0 I, at every block. Here sigma(false)=-1 and sigma(true)=1 are proof signs.")),
                    Paragraph(Text("Set lambda=min(1,D0/(2 exp(1) V0)), A=log(1/alpha)/lambda, H=ceil(A/delta) using the integer ceiling, b=H delta, and G=exitTime(S,b). These are the original constants; positivity and A<=b<=A+1/2 are derived. For every finite n and sample, |S(min(n,G))|<=b+1<=A+3/2. Under each law i, {n<G} is F(n)-measurable and E_i[sigma(i) S(min(n,G))]=(Delta/2) E_i[min(n,G)]. The same G is finite almost surely under each law, its real cast is integrable, and E_i G<=2(A+3/2)/Delta.")),
                    Paragraph(Text("For each i, every finite stopped exponential exp(-lambda sigma(i) S(min(n,G))) has expectation at most one, and the limiting exp(-lambda sigma(i) S(G)) has expectation at most one. The wrong-exit event {sigma(i) S(G)<=-b} has probability at most exp(-lambda b)<=alpha. For i=false this is the upper exit S(G)>=b; for i=true it is the lower exit S(G)<=-b. Both statements use one score path and threshold; no sign is an input to the controller.")),
                    Paragraph(Text("The one-step estimate uses exp(lambda u)<=1+lambda u+(exp(1)/2)lambda^2 u^2 for |u|<=1 and 0<=lambda<=1, derived from Mathlib's exponential remainder bound. Conditional first and second moments give the exponential supermartingale. The proof obtains finite G from the finite drift and monotone convergence before passing to the risk limit. The deterministic overshoot bound dominates the stopped exponentials for bounded convergence. Markov's integral inequality then bounds each wrong exit.")),
                    Paragraph(Text("For the actual source, I=s^(2r) J and delta=J/2^(rJ). The relevant filtration contains the initial wait and completed joint gap/coin blocks, and S is the literal table's completed-block evidence. Identifying emitted wrong labels with these wrong exits uses the same-run finite-gap realization. The payment identity below applies to this execution once its gap exit is almost surely finite and integrable."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("criticalrenewalpayment-actual-source-payment"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPayment.actual_source_payment"),
                H("Exact paid means on the same execution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural r at least one, positive real c and s, positive natural H, natural J and one immutable Tick J, use the two gapLaw and waitLaw probability mass functions of CriticalRenewalSource. For each label separately, assume almost-sure finiteness of gapStop and integrability of its real natural-value projection under sourceLaw. Then paidStop is almost surely finite and its real natural-value projection is integrable under that same law. Its expectation is exactly one plus beta plus mean times the expectation of the natural-value projection of gapStop. The Tick argument precedes the label quantifier, so both conclusions concern the same table.")),
                    Paragraph(Text("The zero-indexed block n is undertaken exactly when all evidence prefixes through n remain strictly between the integer thresholds. This event uses only the first n duration-mark pairs. The next duration is the first coordinate of pair n. The independent-pair law fresh_same_source therefore factors the expected included duration into its actual cycle mean times the inclusion probability. No factorization separates a duration from its own phase or tick increment, or from the decision after its closing tick.")),
                    Paragraph(Text("The included duration is the number of zeros in that very block plus one. Nonnegative summation exchanges expectation and the series of included durations. On each finite exit path, stopped_prefix_payment identifies their sum with the uninterrupted consecutive-bit execution. Its initial contribution is the equilibrium wait plus the first tick; every zero after phase death and the final closing tick is charged. The first wait has the derived equilibrium distribution rather than the iid gap distribution.")),
                    Paragraph(Text("The stopping times retain their infinite value on nonterminating paths. Natural-value projections are used only after almost-sure gap exit is supplied. The source moments and equilibrium wait expectation are derived by source_laws. The payment argument requires neither independence of gapStop and durations nor a source reset. Numerical gap-exit and risk estimates require separate drift and moment bounds for this same table and source."))),
                DescribeRole.Theorem)))));
}
