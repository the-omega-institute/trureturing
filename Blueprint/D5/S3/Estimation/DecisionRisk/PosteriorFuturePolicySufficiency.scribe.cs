using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class PosteriorFuturePolicySufficiencyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/DecisionRisk/PosteriorFuturePolicySufficiency."
            + "posterior_future_policy_universal_sufficiency";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal posteriors give equal conditional Bayes values for every future policy.",
        H("Posterior Future-Policy Sufficiency"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("posterior-future-policy-sufficiency"),
                DeclarationHandle.Create(Declaration),
                H("The posterior is universally sufficient for future-policy Bayes value"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A finite hidden-state joint weight constructs the canonical posterior "
                            + "of each history. The future experiment semantics are supplied as "
                            + "a policy-indexed family of state-conditioned PMFs on an arbitrary "
                            + "complete future-transcript carrier.")),
                    Paragraph(Text(
                        "For a fixed future policy, a terminal decision may depend on the entire "
                            + "future transcript. Its conditional risk mixes the supplied loss "
                            + "over the current posterior and that policy's transcript law; the "
                            + "conditional Bayes value is the infimum over all such decisions.")),
                    Paragraph(Text(
                        "The theorem quantifies every policy, action carrier, and nonnegative "
                            + "extended-real loss publicly. Replacing one history by another with "
                            + "the same posterior leaves the complete displayed value unchanged."))),
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
        Formula policyType = F.Id("P");
        Formula futureType = F.Id("F");
        Formula actionType = F.Id("A");
        Formula joint = F.Id("joint");
        Formula futureLaw = F.Id("Q");
        Formula firstHistory = F.Id("h");
        Formula secondHistory = F.Id("hPrime");
        Formula policy = F.Id("policy");
        Formula loss = F.Id("ell");
        Formula decision = F.Id("d");
        Formula theta = F.Id("theta");
        Formula future = F.Id("f");
        Formula ennreal = F.Id("ENNReal");
        Formula Posterior(Formula history) => Call("posterior", joint, history);
        Formula PosteriorMass(Formula history) => Apply(Posterior(history), theta);
        Formula transcriptLoss = Seq(
            Apply(Apply(Apply(futureLaw, policy), theta), future), Sp, Cdot, Sp,
            Apply(Apply(loss, theta), Apply(decision, future)));
        Formula ConditionalValue(Formula history) =>
            Call("inf", decision,
                Call("sum", theta,
                    Seq(PosteriorMass(history), Sp, Cdot, Sp,
                        Call("tsum", future, transcriptLoss))));
        Formula samePosterior = Seq(
            Posterior(firstHistory), Sp, Eq, Sp, Posterior(secondHistory));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, hidden, Comma, Sp, historyType, Comma, Sp,
            policyType, Comma, Sp, futureType, Comma, RowBreak, Grp(),
            Call("Fintype", hidden), Comma, RowBreak, Grp(),
            joint, Colon, Sp, hidden, Sp, To, Sp,
            historyType, Sp, To, Sp, F.Id("NNReal"), Comma, RowBreak, Grp(),
            futureLaw, Colon, Sp, policyType, Sp, To, Sp,
            hidden, Sp, To, Sp, Call("PMF", futureType), Comma, RowBreak, Grp(),
            firstHistory, Comma, Sp, secondHistory, Colon, Sp, historyType,
            Comma, RowBreak, Grp(),
            samePosterior, Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, policy, Colon, Sp, policyType, Comma, Sp,
            actionType, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma,
            RowBreak, Grp(),
            loss, Colon, Sp, hidden, Sp, To, Sp,
            actionType, Sp, To, Sp, ennreal, Comma, RowBreak, Grp(),
            ConditionalValue(firstHistory), Sp, Eq, Sp,
            ConditionalValue(secondHistory), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
