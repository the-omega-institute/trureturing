using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class CausalPosteriorSufficiencyDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/DecisionRisk/CausalPosteriorSufficiency."
            + "causal_posterior_determines_predictions_and_bayes_decisions";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite causal posterior determines future predictions and Bayes decisions.",
        H("Causal Posterior Sufficiency"),
        Blocks(Describe.Lean(
            DescribeId.Create("causal-posterior-determines-predictions-and-bayes-decisions"),
            DeclarationHandle.Create(Declaration),
            H("The causal posterior determines prediction and decision"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The model carrier is finite and histories induce the canonical normalized "
                        + "posterior from their joint weights. A future law is indexed only by the "
                        + "selected intervention and true model, so it contains no direct history "
                        + "argument.")),
                Paragraph(Text(
                    "The first displayed conclusion constructs every future-output predictive "
                        + "mass by mixing that model-conditioned law against the current posterior. "
                        + "Thus every intervention and output is covered publicly.")),
                Paragraph(Text(
                    "The second conclusion constructs posterior expected loss for every "
                        + "output-dependent decision rule and equates the full sets of minimizers. "
                        + "This states Bayes-decision sufficiency directly, rather than exposing "
                        + "only an optimal value."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula modelType = F.Id("M");
        Formula historyType = F.Id("H");
        Formula interventionType = F.Id("I");
        Formula futureType = F.Id("Y");
        Formula actionType = F.Id("A");
        Formula joint = F.Id("w");
        Formula futureLaw = F.Id("L");
        Formula history = F.Id("h");
        Formula otherHistory = Seq(F.Id("h"), Apos);
        Formula intervention = F.Id("i");
        Formula future = F.Id("y");
        Formula model = F.Id("m");
        Formula loss = F.Id("ell");
        Formula decision = F.Id("d");
        Formula alternative = Seq(F.Id("d"), Apos);
        Formula type = F.Id("Type");
        Formula ennreal = F.Id("ENNReal");

        Formula Posterior(Formula h) => Call("posterior", joint, h);
        Formula PosteriorMass(Formula h) => Apply(Posterior(h), model);
        Formula ConditionalMass() =>
            Apply(Apply(Apply(futureLaw, intervention), model), future);
        Formula PredictiveMass(Formula h) => Call("sum", model,
            Seq(PosteriorMass(h), Sp, Times, Sp, ConditionalMass()));
        Formula DecisionLoss(Formula rule) =>
            Apply(Apply(loss, model), Apply(rule, future));
        Formula BayesCost(Formula h, Formula rule) => Call("sum", model,
            Seq(PosteriorMass(h), Sp, Times, Sp,
                Call("tsum", future,
                    Seq(ConditionalMass(), Sp, Times, Sp, DecisionLoss(rule)))));
        Formula Optimizers(Formula h) => Call("setOf", decision,
            Seq(Forall, Sp, alternative, Colon, Sp,
                futureType, Sp, To, Sp, actionType, Comma, Sp,
                BayesCost(h, decision), Sp, Leq, Sp, BayesCost(h, alternative)));

        Formula predictions = Seq(
            Forall, Sp, intervention, Colon, Sp, interventionType, Comma, Sp,
            future, Colon, Sp, futureType, Comma, Sp,
            PredictiveMass(history), Sp, Eq, Sp, PredictiveMass(otherHistory));
        Formula decisions = Seq(
            Forall, Sp, intervention, Colon, Sp, interventionType, Comma, Sp,
            actionType, Colon, Sp, type, Comma, Sp,
            loss, Colon, Sp, modelType, Sp, To, Sp, actionType, Sp, To, Sp, ennreal,
            Comma, Sp, Optimizers(history), Sp, Eq, Sp, Optimizers(otherHistory));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, modelType, Comma, Sp, historyType, Comma, Sp,
            interventionType, Comma, Sp, futureType, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            Call("Fintype", modelType), Comma, Sp,
            joint, Colon, Sp, modelType, Sp, To, Sp, historyType, Sp, To, Sp,
            F.Id("NNReal"), Comma,
            RowBreak, Grp(),
            futureLaw, Colon, Sp, interventionType, Sp, To, Sp, modelType,
            Sp, To, Sp, Call("PMF", futureType), Comma,
            RowBreak, Grp(),
            history, Comma, Sp, otherHistory, Colon, Sp, historyType, Comma, Sp,
            Posterior(history), Sp, Eq, Sp, Posterior(otherHistory), Sp, Rightarrow,
            RowBreak, Grp(),
            Open, predictions, Close,
            RowBreak, Grp(), Land, RowBreak, Grp(),
            Open, decisions, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
