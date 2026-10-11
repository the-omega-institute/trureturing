using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class ConditionalClockMomentComparisonDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Chernoff =
        LibraryNoteRef.Create("D5/L/Dynamics/howard2020timeuniform");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive conditional clock drift gives geometric tails and real-order moment comparisons for stopped executions.",
        H("Conditional clock drift and adaptive acquisition tails"),
        Blocks(
            Paragraph(Text("Actions A and answers Y are arbitrary finite types. A depth-n record is the complete chronological sequence of action and answer pairs, using SharpChallengeInstrument.Record. A source row is a probability mass function on answers for every depth, complete record, and next action. A fixed actual world and request are parameters of these rows. No topology or compactness on the set of worlds is required. The forced policy is any randomized complete-history table, using SharpChallengeInstrument.Policy; it has no world parameter.")),
            Paragraph(Text("historyLaw starts at the unique empty record. At each step it samples the policy action, samples the corresponding history-dependent source row, and appends both draws. The fixed calibration c is a real function of depth, record, action and answer. clock adds these increments along the acquired record. Fix real constants with 0 < mu <= C. Every increment lies in [0,C], and every conditional source row has mean increment at least mu, including rows at unreachable formal histories. Set r = 1 - (mu/C)(1-exp(-1)), a = -(C/2) log r, and rho = sqrt r. These are rate, slope and tailRate, respectively.")),
            Describe.Lean(
                DescribeId.Create("adaptive-laplace-decay"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/ConditionalClockMomentComparison.adaptive_laplace_decay"),
                H("Adaptive conditional Laplace decay"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Chernoff),
                Blocks(
                    Paragraph(Text("For every forced policy and every natural depth n, the finite expectation of exp(-clock/C) under historyLaw is at most r to the power n. The expectation is the sum over all depth-n records of their actual probability masses times exp(-clock/C). The bound holds at depth zero as well.")),
                    Paragraph(Text("Convexity places exp(-x/C) below the chord joining its values at zero and C. Averaging that chord in each source row and using the conditional drift gives the same contraction r. The proof then averages over the actual randomized action row and the current joint history law. The resulting global estimate preserves the dependence of each source and policy on the entire acquired history; no independence between increments is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adaptive-clock-tail"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/ConditionalClockMomentComparison.adaptive_clock_tail"),
                H("Uniform geometric low-clock probability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Chernoff),
                Blocks(
                    Paragraph(Text("Under the same complete hypotheses, 0 < r < 1, a > 0, and 0 < rho < 1. For every natural n the probability under historyLaw that clock is at most a times n is at most rho to the power n. Probability is written as the real value of the PMF outer measure; every set is measurable for this finite discrete law.")),
                    Paragraph(Text("The Chernoff lower-tail inequality is used directly from Mathlib with parameter -1/C. The preceding adaptive Laplace estimate bounds its moment-generating function. Exponential and logarithmic identities give exp(a n/C) r^n = rho^n. The endpoint chord and the one-shot Chernoff inequality are classical tools. Their propagation through the specified adaptive source/history interface is the additional relationship established here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("stopping-prefix-clock-tail"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/ConditionalClockMomentComparison.stopping_prefix_clock_tail"),
                H("Actually acquired prefixes of a stopping policy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Chernoff),
                Blocks(
                    Paragraph(Text("A stopping policy assigns a probability distribution on Option A to every finite acquired record. None returns; some action makes one further source query. Fix any default action a0. acquiredMass is the probability of actually acquiring a specified record: it starts at one and multiplies the continuing-action and source-answer probabilities at every step. Its sum at depth n is the call-depth survival probability.")),
                    Paragraph(Text("For every natural n, the sum of acquiredMass over records with clock at most a times n is at most rho^n. In addition, total acquiredMass at depth n is at most the acquiredMass of records with clock at least a times n plus rho^n. Both statements hold for every randomized stopping table under the same source and drift hypotheses.")),
                    Paragraph(Text("forceQueries replaces each return decision by a query of a0. Each continuing-action probability can only increase. Multiplication along the same source history therefore dominates acquiredMass by the forced history law, without reclassifying any returned execution as a real subsequent acquisition. Splitting the actually acquired prefixes at the clock threshold gives the second inequality.")),
                    Paragraph(Text("These finite-prefix estimates feed the complete-path moment comparison below. The continuing record at every depth is part of the same stopped path."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("stopped-clock-moment-comparison"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/ConditionalClockMomentComparison.stopped_clock_moment_comparison"),
                H("Extended moments of complete stopped paths"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Chernoff),
                Blocks(
                    Paragraph(Text("A StoppedPath has an optional complete acquired record at each natural depth. Its depth-zero record is empty, and every acquired child has its actual parent. Thus return is absorbing. totalCalls is the supremum of acquired depths; totalClock is the supremum of their nonnegative accumulated clocks. A nonterminating path retains its actual cumulative clock, which may be finite or infinite. No almost-sure termination or finite-moment assumption is made.")),
                    Paragraph(Text("StoppedExecution specifies a measure on an arbitrary measurable sample space, a map to complete stopped paths, and all acquired cylinder masses. For every depth and predicate on records, the cylinder is measurable and its probability is the sum of acquiredMass over the selected records. Its root condition forces total mass one. These are assumptions identifying the execution law. Existence of such a realization for every history-dependent PMF table is a separate construction.")),
                    Paragraph(Text("For every index family I of worlds and requests, arbitrary corresponding measurable sample spaces and StoppedExecution realizations, and any real s > 0, assume the same constants 0 < mu <= C bound every increment and every conditional source-row mean. Define momentWeight(s,n) = (n+1)^s - n^s in the extended nonnegative reals and momentError(s,rho) as the sum over n >= 0 of momentWeight(s,n) times rho^(n+1). This is exactly A_s with its index shifted by one, and it is finite.")),
                    Paragraph(Text("For each index, the expected s-th clock power is at most C^s times the expected s-th call-count power. Conversely, the expected s-th call-count power is at most a^(-s) times the expected s-th clock power plus A_s. Both are extended-real inequalities. The supremum over all indices of the clock moment is finite if and only if the supremum of the call-count moment is finite. The theorem permits the source rows, policies and calibrations to vary with the index; a common policy and calibration are included by specialization.")),
                    Paragraph(Text("The complete-path call power is the nonnegative sum of moment weights over acquired depths. Cylinder probabilities transfer the finite-prefix tail estimate to the actual final clock. Tonelli then interchanges the countable sum and expectation. Every finite partial sum selected by the threshold n <= T/a is bounded by (T/a)^s; this also holds when T is infinite. Polynomial times geometric summability makes A_s finite. In the other direction, each acquired clock is bounded by C times its depth, so the same bound holds for the two suprema and their positive powers."))),
                DescribeRole.Theorem))));
}
