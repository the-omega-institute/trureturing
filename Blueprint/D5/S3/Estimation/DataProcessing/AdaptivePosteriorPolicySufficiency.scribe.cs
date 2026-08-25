using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class AdaptivePosteriorPolicySufficiencyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/DataProcessing/AdaptivePosteriorPolicySufficiency."
            + "posterior_adaptive_policy_universal_sufficiency";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal posteriors generate equal adaptive future laws and recursive Bayes values.",
        H("Adaptive Posterior-Policy Sufficiency"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("adaptive-posterior-policy-sufficiency"),
                DeclarationHandle.Create(Declaration),
                H("The posterior determines adaptive future laws and continuation values"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The experiment kernel is state-conditioned, while the finite-horizon "
                            + "policy selects each next experiment from the current posterior. "
                            + "Observed outputs extend the actual history.")),
                    Paragraph(Text(
                        "The displayed conditioning premise requires every extended-history "
                            + "posterior to be the canonical Bayes update of the current "
                            + "posterior by the selected experiment kernel.")),
                    Paragraph(Text(
                        "Induction on the horizon first transports that update through equal "
                            + "posteriors, then identifies both the recursively generated "
                            + "future-output law and the predictive continuation sum.")),
                    Paragraph(Text(
                        "At horizon zero the continuation value is the infimum of posterior "
                            + "expected loss over the arbitrary action carrier. Thus both "
                            + "conclusions hold for every policy, action type, loss, and finite "
                            + "horizon."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula TheoremFormula()
    {
        Formula hidden = F.Id("Theta");
        Formula historyType = F.Id("H");
        Formula experimentType = F.Id("E");
        Formula observationType = F.Id("Y");
        Formula actionType = F.Id("A");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula nnreal = F.Id("NNReal");
        Formula ennreal = F.Id("ENNReal");
        Formula joint = F.Id("j");
        Formula extend = F.Id("extend");
        Formula kernel = F.Id("K");
        Formula policy = F.Id("policy");
        Formula loss = F.Id("ell");
        Formula horizon = F.Id("n");
        Formula history = F.Id("h");
        Formula otherHistory = F.Id("hPrime");
        Formula selectedExperiment = F.Id("e");
        Formula observation = F.Id("y");
        Formula state = F.Id("theta");
        Formula output = F.Id("o");
        Formula Posterior(Formula atHistory) => Call("posterior", joint, atHistory);
        Formula extension = Apply(extend, history, selectedExperiment, observation);
        Formula likelihood = Seq(
            Open, state, Comma, Sp, output, Close, Sp, Mapsto, Sp,
            Call("toNNReal", Apply(kernel, selectedExperiment, state, output)));
        Formula conditioned = Seq(
            Forall, Sp, history, Colon, Sp, historyType, Comma, Sp,
            selectedExperiment, Colon, Sp, experimentType, Comma, Sp,
            observation, Colon, Sp, observationType, Comma, RowBreak, Grp(),
            Posterior(extension), Sp, Eq, Sp,
            Call("posteriorUpdate", likelihood, Posterior(history), observation));
        Formula futureLaw(Formula atHistory) => Call(
            "adaptiveFutureOutputLaw", joint, extend, kernel, policy, horizon, atHistory);
        Formula continuation(Formula atHistory) => Call(
            "adaptiveContinuationValue", joint, extend, kernel, policy, loss,
            horizon, atHistory);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, hidden, Comma, Sp, historyType, Comma, Sp,
            experimentType, Comma, Sp, observationType, Colon, Sp, type,
            Comma, RowBreak, Grp(),
            Call("Fintype", hidden), Comma, RowBreak, Grp(),
            joint, Colon, Sp, hidden, Sp, To, Sp, historyType, Sp, To, Sp,
            nnreal, Comma, RowBreak, Grp(),
            extend, Colon, Sp, historyType, Sp, To, Sp, experimentType, Sp,
            To, Sp, observationType, Sp, To, Sp, historyType,
            Comma, RowBreak, Grp(),
            kernel, Colon, Sp, experimentType, Sp, To, Sp, hidden, Sp,
            To, Sp, Call("PMF", observationType), Comma, RowBreak, Grp(),
            conditioned, Comma, RowBreak, Grp(),
            history, Comma, Sp, otherHistory, Colon, Sp, historyType, Comma, Sp,
            Posterior(history), Sp, Eq, Sp, Posterior(otherHistory),
            Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, policy, Colon, Sp, natural, Sp, To, Sp,
            Open, hidden, Sp, To, Sp, nnreal, Close, Sp, To, Sp,
            experimentType, Comma, RowBreak, Grp(),
            actionType, Colon, Sp, type, Comma, Sp,
            loss, Colon, Sp, hidden, Sp, To, Sp, actionType, Sp, To, Sp,
            ennreal, Comma, Sp, horizon, Colon, Sp, natural, Comma,
            RowBreak, Grp(),
            futureLaw(history), Sp, Eq, Sp, futureLaw(otherHistory),
            Sp, Land, RowBreak, Grp(),
            continuation(history), Sp, Eq, Sp, continuation(otherHistory), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
