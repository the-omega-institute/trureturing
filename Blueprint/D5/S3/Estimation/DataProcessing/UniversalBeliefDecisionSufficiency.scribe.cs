using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class UniversalBeliefDecisionSufficiencyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/DataProcessing/UniversalBeliefDecisionSufficiency."
            + "task_independent_belief_sufficiency";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A belief identifies Bayes value simultaneously for every future decision task.",
        H("Universal Belief Decision Sufficiency"),
        Blocks(Describe.Lean(
            DescribeId.Create("universal-belief-decision-sufficiency"),
            DeclarationHandle.Create(Declaration),
            H("The belief quotient is sufficient for every Bayes decision problem"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Histories map to probability measures on an arbitrary measurable hidden "
                        + "state. Each future policy supplies a Markov kernel from that state "
                        + "to a complete future transcript.")),
                Paragraph(Text(
                    "A terminal decision may depend on the entire future transcript. The "
                        + "displayed infimum explicitly ranges over rules d from F to A.")),
                Paragraph(Text(
                    "Equality of two history posteriors preserves this value for every policy, "
                        + "action carrier, and nonnegative extended-real loss simultaneously."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula hiddenType = F.Id("X");
        Formula historyType = F.Id("H");
        Formula policyType = F.Id("P");
        Formula futureType = F.Id("F");
        Formula actionType = F.Id("A");
        Formula posterior = F.Id("pi");
        Formula futureLaw = F.Id("Q");
        Formula kernel = F.Id("kappa");
        Formula history = F.Id("h");
        Formula otherHistory = Seq(F.Id("h"), Apos);
        Formula policy = F.Id("p");
        Formula loss = F.Id("ell");
        Formula decision = F.Id("d");
        Formula hidden = F.Id("x");
        Formula future = F.Id("f");
        Formula type = F.Id("Type");

        Formula Posterior(Formula h) => Apply(posterior, h);
        Formula PolicyKernel() => Apply(futureLaw, policy);
        Formula KernelMeasure() => Apply(PolicyKernel(), hidden);
        Formula ConditionalRisk(Formula h) => Call("lintegral", hidden,
            Call("lintegral", future,
                Apply(Apply(loss, hidden), Apply(decision, future)), KernelMeasure()),
            Posterior(h));
        Formula BayesValue(Formula h) => Seq(
            Operatorname, Grp(F.Id("inf")), Underscore,
            Grp(decision, Colon, Sp, futureType, Sp, To, Sp, actionType), Sp,
            ConditionalRisk(h));
        Formula markovKernelCarrier = Seq(
            OpenBrace, kernel, Colon, Sp, Call("Kernel", hiddenType, futureType), Sp,
            Mid, Sp, Call("IsMarkovKernel", kernel), CloseBrace);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, hiddenType, Comma, Sp, historyType, Comma, Sp,
            policyType, Comma, Sp, futureType, Colon, Sp, type, Comma, RowBreak, Grp(),
            Call("MeasurableSpace", hiddenType), Comma, Sp,
            Call("MeasurableSpace", futureType), Comma, RowBreak, Grp(),
            posterior, Colon, Sp, historyType, Sp, To, Sp,
            Call("ProbabilityMeasure", hiddenType), Comma, RowBreak, Grp(),
            futureLaw, Colon, Sp, policyType, Sp, To, Sp,
            markovKernelCarrier, Comma, RowBreak, Grp(),
            history, Comma, Sp, otherHistory, Colon, Sp, historyType, Comma, RowBreak, Grp(),
            Posterior(history), Sp, Eq, Sp, Posterior(otherHistory), Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, policy, Colon, Sp, policyType, Comma, Sp,
            actionType, Colon, Sp, type, Comma, RowBreak, Grp(),
            loss, Colon, Sp, hiddenType, Sp, To, Sp,
            actionType, Sp, To, Sp, F.Id("ENNReal"), Comma, RowBreak, Grp(),
            BayesValue(history), Sp, Eq, Sp, BayesValue(otherHistory), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
