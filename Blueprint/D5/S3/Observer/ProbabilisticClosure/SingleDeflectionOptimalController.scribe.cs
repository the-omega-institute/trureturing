using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class SingleDeflectionOptimalControllerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/SingleDeflectionOptimalController.";

    public DocumentDefinition Create()
    {
        Formula mu = F.Id("mu");
        Formula threshold = F.Id("N");
        Formula machine = F.Id("C");
        Formula seedType = F.Id("U");
        Formula otherType = F.Id("V");
        Formula seed = F.Id("u");
        Formula source = F.Id("s");
        Formula law = F.Id("nu");
        Formula otherLaw = F.Id("rho");
        Formula competitor = F.Id("p");
        Formula state = F.Id("x");
        Formula reply = F.Id("r");
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        Formula k = F.Id("k");
        Formula none = F.Id("none");
        Formula truth = F.Id("true");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula interval = Seq(OpenBracket, D(0), Comma, D(1), CloseBracket);
        Formula memory = Call("Memory", machine);
        Formula policy = Call("controllerPolicy", machine);
        Formula moment = Call("reciprocalMoment", mu);
        Formula first = Call("firstNegative", Alpha, mu);
        Formula oneMinusAlpha = Seq(Open, D(1), Minus, Alpha, Close);
        Formula twiceM = Seq(D(2), m);
        Formula run = Call("controlledRun", machine, source, n);
        Formula actual = Call("actualRun", policy, seed, source, n);
        Formula replay = Call("zeroReplay", policy, seed, twiceM);

        Formula Par(Formula body) => Seq(Open, body, Close);
        Formula All(Formula variable, Formula type, Formula body) => Seq(
            Forall, Sp, variable, Colon, type, Comma, Sp, Par(body));
        Formula Imp(Formula premise, Formula body) => Seq(premise, Rightarrow, Par(body));
        Formula V(Formula index) => Call("coefficient", Alpha, mu, index);
        Formula Action(Formula value) => Call("action", machine, value);
        Formula Update(Formula value, Formula response) => Call("update", machine, value, response);
        Formula Cost(Formula p, Formula measure) => Call("expectedCost", p, measure, Alpha, mu);
        Formula Lambda(Formula index) => Call("lambda", policy, law, index);
        Formula TailIndicator(Formula index) => Call("ite", Seq(threshold, Leq, Sp, index), D(1), D(0));
        Formula Some(Formula value) => Call("some", value);
        Formula SeedSpace(Formula type, Formula body) => All(type, F.Id("Type"),
            Imp(Call("MeasurableSpace", type), body));
        Formula SeedLaw(Formula type, Formula measure, Formula body) => SeedSpace(type,
            All(measure, Call("Measure", type), Imp(Call("IsProbabilityMeasure", measure), body)));
        Formula PositiveIndex(Formula index, Formula body) => All(index, naturals,
            Imp(Seq(D(1), Leq, Sp, index), body));

        Formula noNegative = Seq(threshold, Eq, Infty, Leftrightarrow,
            PositiveIndex(m, Seq(D(0), Leq, V(m))));
        Formula finiteThreshold = All(k, naturals, Imp(Seq(threshold, Eq, k), Seq(
            D(1), Leq, Sp, k, Land, Sp,
            Par(PositiveIndex(m, Seq(V(m), Lt, D(0), Leftrightarrow, Sp, k, Leq, Sp, m))), Land, Sp,
            Call("card", memory), Eq, D(2), k, Plus, D(2))));
        Formula infiniteSize = Imp(Seq(threshold, Eq, Infty), Seq(Call("card", memory), Eq, D(2)));
        Formula sink = All(state, memory, All(reply, F.Id("Bool"),
            Imp(Seq(Action(state), Eq, none), Seq(Update(state, reply), Eq, state))));
        Formula marker = All(state, memory, Seq(Action(Update(state, truth)), Eq, none));
        Formula stopped = Call("stopped", actual);
        Formula runMemory = Call("memory", run);
        Formula schedule = Call("plannedSide", threshold, n);
        Formula refinement = SeedSpace(seedType, All(seed, seedType,
            All(source, F.Id("Source"), All(n, naturals, Seq(
                Call("trace", run), Eq, actual, Land, Sp,
                runMemory, Eq, Call("foldl", Call("update", machine), Call("initial", machine),
                    Call("reverse", Call("replies", actual))), Land, Sp,
                Action(runMemory), Eq, Call("ite", Seq(stopped, Eq, truth), none, Some(schedule)), Land, Sp,
                Par(Imp(Seq(Action(runMemory), Eq, none), Seq(
                    Call("controlledRun", machine, source, Seq(n, Plus, D(1))), Eq, run))))))));
        Formula counts = SeedSpace(seedType, All(seed, seedType, PositiveIndex(m, Seq(
            Call("pair", Call("sideCount", replay, F.Id("false")),
                Call("sideCount", replay, truth)), Eq,
            Call("ite", Seq(threshold, Leq, Sp, m),
                Call("pair", Seq(twiceM, Minus, D(1)), D(1)), Call("pair", twiceM, D(0)))))));
        Formula minimumSum = Seq(Sum, Underscore, Grp(n, Eq, D(0)), Caret, Grp(Infty),
            Call("min", D(0), V(Seq(n, Plus, D(1)))));
        Formula optimum = SeedLaw(seedType, law, Seq(
            Par(PositiveIndex(m, Seq(Lambda(m), Eq, TailIndicator(m)))), Land, Sp,
            Cost(policy, law), Neq, Infty, Land, Sp,
            Call("toReal", Cost(policy, law)), Eq,
                D(2), Call("toReal", moment), Minus, oneMinusAlpha, Plus, minimumSum, Land, Sp,
            Par(SeedLaw(otherType, otherLaw, All(competitor, Call("Policy", otherType), Seq(
                Cost(policy, law), Leq, Cost(competitor, otherLaw)))))));
        Formula body = Seq(
            F.Id("let"), Sp, threshold, Eq, first, Comma, Sp,
            machine, Eq, Call("controller", threshold), Sp, F.Id("in"), Sp,
            RowBreak, Grp(), Par(noNegative), Land, Sp,
            RowBreak, Grp(), Par(finiteThreshold), Land, Sp,
            RowBreak, Grp(), Par(infiniteSize), Land, Sp,
            RowBreak, Grp(), Par(sink), Land, Sp,
            RowBreak, Grp(), Par(marker), Land, Sp,
            RowBreak, Grp(), Par(refinement), Land, Sp,
            RowBreak, Grp(), Par(counts), Land, Sp,
            RowBreak, Grp(), Par(optimum));
        Formula finiteMean = Imp(Seq(moment, Neq, Infty), body);
        Formula support = Imp(Call("AE", mu,
            Par(Seq(D(0), Lt, F.Id("Q"), Land, Sp, F.Id("Q"), Lt, D(1)))), finiteMean);
        Formula prior = All(mu, Call("Measure", interval), Imp(Call("IsProbabilityMeasure", mu), support));
        Formula parameters = All(Alpha, interval,
            Imp(Seq(D(0), Lt, Alpha, Land, Sp, Alpha, Lt, D(1)), prior));
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")), parameters, End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A single-deflection finite-state controller attaining the actual marker-stopping minimum.",
            H("Internally maintained finite memory and the fixed-prior optimum"),
            Blocks(Describe.Lean(
                DescribeId.Create("single-deflection-optimal-controller"),
                DeclarationHandle.Create(Prefix + "single_deflection_optimal_controller"),
                H("Complete finite and infinite threshold branches with actual-source refinement"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The prior mu is any probability measure on the closed unit interval with 0<Q<1 "
                        + "almost everywhere, alpha is strictly between zero and one, and reciprocalMoment(mu) "
                        + "is finite. coefficient(alpha,mu,m) is the original integral of "
                        + "(1-Q)(alpha-(1-alpha)Q)Q^(m-1). N is the original WithTop infimum of positive "
                        + "negative-coefficient indices. Natural thresholds are embedded into WithTop in the formulas. "
                        + "The empty negative set has threshold infinity. Dirac priors, nondegenerate priors, "
                        + "zero coefficients and all ties remain within the same hypotheses.")),
                    Paragraph(Text(
                        "The coefficient tail follows without a nondegeneracy assumption: alpha times v_m "
                        + "minus (1-alpha) times v_(m+1) is the integral of "
                        + "(1-Q)Q^(m-1)(alpha-(1-alpha)Q)^2, which is nonnegative. These polynomials are "
                        + "integrable on the compact unit interval. Thus a negative coefficient forces the "
                        + "next coefficient to be negative. The least positive negative index is Nat.find "
                        + "when such an index exists and equals the original WithTop infimum.")),
                    Paragraph(Text(
                        "For finite N=k, C.Memory is Option Fin(2k-1+2), with 2k+2 total states including "
                        + "the marker sink. The initial state is some(machineEncode(2k-1,0)); a false reply "
                        + "applies the existing saturating machineUpdate, and a true reply enters none. "
                        + "The optional action is right exactly at the counter pulse and left in all other "
                        + "active states. For infinite N, C.Memory is Option Unit, initially some(unit), "
                        + "with the always-left action and the same absorbing marker sink. None emits no action. "
                        + "The delay is internal state, with no external clock input.")),
                    Paragraph(Text(
                        "plannedSide(N,n) is right precisely when N=k is finite and n+1=2k; it is left "
                        + "otherwise. Thus the sole right query is the one-based query 2N. The actual controller "
                        + "updates its memory once per acquired reply. controlledRun records that memory and "
                        + "the environment's acquired trace; the environment supplies the fresh-arm markerResponse "
                        + "using its queried arm counts. It does not supply a clock to the controller. In the "
                        + "formulas memory and trace are the first and second controlledRun projections.")),
                    Paragraph(Text(
                        "controllerPolicy is the original measurable Policy adapter: it folds acquired replies "
                        + "chronologically from C.initial and reads C.action, using left as a dormant default "
                        + "when the action is none. The source histories are newest first, so the fold reverses "
                        + "the reply list. For every seed, source and horizon, controlledRun has exactly the "
                        + "original actualRun trace and its memory is exactly this reply fold. Its action is none "
                        + "exactly after stopping and otherwise is some(plannedSide(N,n)). The marker-producing "
                        + "query is included in the trace; the halted machine performs no later query.")),
                    Paragraph(Text(
                        "At every positive even replay depth 2m, the same constructed policy has the joint "
                        + "left/right count pair (2m,0) before N and (2m-1,1) from N onward. Lambda is measured "
                        + "under the original arbitrary independent seed probability law, without survival "
                        + "conditioning, and equals the indicator of N<=m. The source execution refinement and "
                        + "the frozen exact counter readout are used to obtain these common-route counts.")),
                    Paragraph(Text(
                        "expectedCost retains the original nonnegative integral of actual stoppingTime under "
                        + "priorLaw, the original prior bind of the independent-seed joint source law. The attained "
                        + "real cost is 2 reciprocalMoment(mu).toReal-(1-alpha) plus the absolutely summable "
                        + "sum of min(0,coefficient(alpha,mu,n+1)). Finiteness is established before converting "
                        + "to real costs. The extended expectation is no greater than that of every legal Policy "
                        + "on any other measurable seed space with any original independent probability law.")),
                    Paragraph(Text(
                        "This is fixed-prior finite-state existence for choosing directions, immediate stopping "
                        + "and the mean objective. It gives no procedure to decide N from an arbitrary approximate "
                        + "prior representation, no finite exact predictor dimension, no optimal-policy uniqueness, "
                        + "no uniform state bound over priors and no state-minimality claim."))),
                DescribeRole.Theorem))));
    }
}
