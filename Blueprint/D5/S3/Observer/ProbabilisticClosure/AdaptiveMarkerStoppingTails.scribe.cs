using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class AdaptiveMarkerStoppingTailsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.";

    public DocumentDefinition Create()
    {
        Formula policy = F.Id("p");
        Formula seed = F.Id("u");
        Formula source = F.Id("s");
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula m = F.Id("m");
        Formula q = F.Id("q");
        Formula law = F.Id("v");
        Formula seedType = F.Id("U");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula tau = Call("stoppingTime", policy, seed, source);
        Formula run = Call("actualRun", policy, seed, source, n);
        Formula replay = Call("zeroReplay", policy, seed, n);
        Formula noMarker = Call("prefixNoMarker", source, replay);
        Formula active = Seq(Call("stopped", run), Eq, F.Id("false"));
        Formula stopped = Seq(Call("stopped", run), Eq, F.Id("true"));
        Formula cost = Call("actualQueryCount", policy, seed, source, n);
        Formula bridge = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, seedType, Colon, F.Id("Type"), Comma, Sp,
            Open, Call("MeasurableSpace", seedType), Rightarrow, Open,
            RowBreak, Grp(),
            Forall, Sp, policy, Colon, Call("Policy", seedType), Comma, Sp,
            Forall, Sp, seed, Colon, seedType, Comma, Sp,
            Forall, Sp, source, Colon, F.Id("Source"), Comma, Sp,
            Forall, Sp, n, InMacro, naturals, Comma, RowBreak, Grp(),
            Open,
            Open, Open, n, Lt, tau, Close, Leftrightarrow, noMarker, Close,
            Land, RowBreak, Grp(),
            Open, Open, active, Close, Leftrightarrow, noMarker, Close,
            Land, RowBreak, Grp(),
            Open, Open, active, Close, Rightarrow, Open,
                Open, Call("actions", run), Eq, replay, Close, Land,
                Open, Call("replies", run), Eq, Call("replicate", n, F.Id("false")), Close, Land,
                Open, cost, Eq, n, Close, Close, Close,
            Land, RowBreak, Grp(),
            Open, Open, stopped, Close, Rightarrow, Open,
                Forall, Sp, k, InMacro, naturals, Comma, Sp,
                Open, Call("actualRun", policy, seed, source, Seq(n, Plus, k)), Eq, run,
                Close, Close, Close,
            Land, RowBreak, Grp(),
            Open, Call("noAdjacentOnes", source), Rightarrow, Open,
                Open, n, Lt, tau, Close, Leftrightarrow,
                Call("alternatingPrefixes", source, replay), Close, Close,
            Land, RowBreak, Grp(),
            Open, cost, Eq, Call("min", n, tau), Close,
            Close, Close, Close, Dot,
            End, Grp(F.Id("gathered"))));

        Formula joint = Call("jointLaw", law, Alpha, q);
        Formula lambda = Call("lambda", policy, law, m);
        Formula qm = Seq(q, Caret, Grp(m));
        Formula qmPrev = Seq(q, Caret, Grp(Seq(m, Minus, D(1))));
        Formula qSquared = Seq(q, Caret, Grp(D(2)));
        Formula a = Seq(Open, D(1), Minus, Alpha, Close);
        Formula oddDepth = Seq(D(2), m, Plus, D(1));
        Formula evenDepth = Seq(D(2), m);
        Formula tails = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, seedType, Colon, F.Id("Type"), Comma, Sp,
            Open, Call("MeasurableSpace", seedType), Rightarrow, Open,
            RowBreak, Grp(),
            Forall, Sp, law, Colon, Call("Measure", seedType), Comma, Sp,
            Open, Call("ProbabilityMeasure", law), Rightarrow, Open,
            RowBreak, Grp(),
            Forall, Sp, policy, Colon, Call("Policy", seedType), Comma, Sp,
            Forall, Sp, Alpha, InMacro,
            OpenBracket, D(0), Comma, D(1), CloseBracket, Comma, Sp,
            Forall, Sp, q, InMacro,
            OpenBracket, D(0), Comma, D(1), CloseBracket, Comma, RowBreak, Grp(),
            Open,
            Open, Forall, Sp, m, InMacro, naturals, Comma, Sp,
            Call("Tail", joint, policy, oddDepth), Eq,
            Open, Alpha, Plus, a, q, Close, qm, Close,
            Land, RowBreak, Grp(),
            Open, Forall, Sp, m, InMacro, naturals, Comma, Sp,
            Open, Open, D(1), Leq, Sp, m, Close, Rightarrow, Open,
            Call("Tail", joint, policy, evenDepth), Eq,
            qm, Plus, lambda, Open, Alpha, Plus, a, qSquared, Minus, q, Close,
            qmPrev, Close, Close, Close,
            Land, RowBreak, Grp(),
            Open, Forall, Sp, m, InMacro, naturals, Comma, Sp,
            D(0), Leq, lambda, Leq, D(1), Close,
            Close, Close, Close, Close, Close, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact adaptive marker tails under a shared-root Markov source and an arbitrary independent seed law.",
            H("Actual stopping, zero replay, and exact tails"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("stopped-execution-replay-bridge"),
                    DeclarationHandle.Create(Prefix + "stopped_execution_replay_bridge"),
                    H("First-hit execution and acquired query cost"),
                    StatementSource.FromAuthor(bridge),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "A policy reads its seed and its acquired action and reply lists, stored newest first. "
                            + "Every active step queries a fresh edge on the chosen arm. The first 00 response stops "
                            + "execution; every later step preserves the complete state and acquires no query.")),
                        Paragraph(Text(
                            "The stopping time is the first actual stopped state, with infinity allowed. "
                            + "Its tail event equals the no-marker prefixes at the arm counts from the same policy's "
                            + "all-zero replay. Replay takes no source argument. Under no adjacent ones, these prefixes "
                            + "are alternating. Acquired query count is the minimum of elapsed steps and first-hit time."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("adaptive-marker-stopping-tails"),
                    DeclarationHandle.Create(Prefix + "adaptive_marker_stopping_tails"),
                    H("Both exact tails with the original-seed odd-odd probability"),
                    StatementSource.FromAuthor(tails),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Tail denotes the real measure of the actual event that stoppingTime exceeds the stated "
                            + "depth. The source law first mixes a Bernoulli root of mass alpha at true. Given this root "
                            + "and one fixed q, its two outward arms are independent Markov trajectories with transition "
                            + "rows (1-q,q) and (1,0). The same q is used for every transition on both arms.")),
                        Paragraph(Text(
                            "The joint law is the product of this source law and the original arbitrary probability "
                            + "measure on the measurable seed space. Policy requires every fixed finite action/reply "
                            + "history gives a measurable seed section; the policy has no hidden-source argument.")),
                        Paragraph(Text(
                            "Lambda is the original seed measure of the event that zeroReplay at depth twice m has "
                            + "odd counts on both arms. Its definition contains no q, source, or survival conditioning. "
                            + "The proof derives trajectory support from the Markov kernel, calculates alternating "
                            + "finite-prefix masses, and integrates the actual survival "
                            + "event over the original seed law. The formulas hold on the closed unit interval and "
                            + "therefore for the chapter's strictly interior parameters."))),
                    DescribeRole.Theorem))));
    }
}
