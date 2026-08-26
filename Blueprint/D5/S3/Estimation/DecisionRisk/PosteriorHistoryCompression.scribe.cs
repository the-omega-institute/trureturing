using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class PosteriorHistoryCompressionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/DecisionRisk/PosteriorHistoryCompression."
            + "posterior_history_compression";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The posterior measure compresses history for prediction and continuation decisions.",
        H("Posterior History Compression"),
        Blocks(Describe.Lean(
            DescribeId.Create("posterior-history-compression"),
            DeclarationHandle.Create(Declaration),
            H("The posterior determines every future decision quantity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Histories are mapped to posterior measures on an arbitrary measurable "
                        + "hidden-state carrier. Future event probabilities depend on a hidden "
                        + "state and selected experiment, never directly on history.")),
                Paragraph(Text(
                    "A loss family constructs Bayes risk by taking the infimum of posterior "
                        + "expected losses. A continuation policy likewise has a posterior "
                        + "expected cost, and the optimal continuation value is the infimum over "
                        + "all such policies.")),
                Paragraph(Text(
                    "The four displayed conclusions separately expose prediction, Bayes risk, "
                        + "every policy cost, and optimal continuation value. Equality of the "
                        + "posterior measures identifies each construction."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula hiddenType = F.Id("X");
        Formula historyType = F.Id("H");
        Formula experimentType = F.Id("I");
        Formula eventType = F.Id("E");
        Formula policyType = F.Id("P");
        Formula actionType = F.Id("A");
        Formula posterior = F.Id("pi");
        Formula eventProbability = F.Id("Q");
        Formula policyCost = F.Id("C");
        Formula loss = F.Id("L");
        Formula history = F.Id("h");
        Formula otherHistory = Seq(F.Id("h"), Apos);
        Formula experiment = F.Id("i");
        Formula eventName = F.Id("e");
        Formula policy = F.Id("p");
        Formula action = F.Id("a");
        Formula hidden = F.Id("x");
        Formula ennreal = F.Id("ENNReal");
        Formula type = F.Id("Type");

        Formula Posterior(Formula h) => Apply(posterior, h);
        Formula EventMass(Formula h) => Call("lintegral", hidden,
            Apply(Apply(Apply(eventProbability, experiment), eventName), hidden), Posterior(h));
        Formula ActionRisk(Formula h) => Call("lintegral", hidden,
            Apply(Apply(loss, action), hidden), Posterior(h));
        Formula PolicyValue(Formula h) => Call("lintegral", hidden,
            Apply(Apply(policyCost, policy), hidden), Posterior(h));
        Formula BayesRisk(Formula h) => Call("inf", action, ActionRisk(h));
        Formula ContinuationValue(Formula h) => Call("inf", policy, PolicyValue(h));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, hiddenType, Comma, Sp, historyType, Comma, Sp,
            experimentType, Comma, Sp, eventType, Comma, Sp, policyType, Comma, Sp,
            actionType, Colon, Sp, type, Comma, RowBreak, Grp(),
            Call("MeasurableSpace", hiddenType), Comma, RowBreak, Grp(),
            posterior, Colon, Sp, historyType, Sp, To, Sp, Call("Measure", hiddenType), Comma,
            RowBreak, Grp(),
            eventProbability, Colon, Sp, experimentType, Sp, To, Sp, eventType, Sp, To, Sp,
            hiddenType, Sp, To, Sp, ennreal, Comma, RowBreak, Grp(),
            policyCost, Colon, Sp, policyType, Sp, To, Sp, hiddenType, Sp, To, Sp, ennreal,
            Comma, RowBreak, Grp(),
            loss, Colon, Sp, actionType, Sp, To, Sp, hiddenType, Sp, To, Sp, ennreal,
            Comma, RowBreak, Grp(),
            history, Comma, Sp, otherHistory, Colon, Sp, historyType, Comma, Sp,
            Posterior(history), Sp, Eq, Sp, Posterior(otherHistory), Sp, Rightarrow,
            RowBreak, Grp(),
            Open, Forall, Sp, experiment, Colon, Sp, experimentType, Comma, Sp,
            eventName, Colon, Sp, eventType, Comma, Sp,
            EventMass(history), Sp, Eq, Sp, EventMass(otherHistory), Close,
            RowBreak, Grp(), Land, RowBreak, Grp(),
            BayesRisk(history), Sp, Eq, Sp, BayesRisk(otherHistory),
            RowBreak, Grp(), Land, RowBreak, Grp(),
            Open, Forall, Sp, policy, Colon, Sp, policyType, Comma, Sp,
            PolicyValue(history), Sp, Eq, Sp, PolicyValue(otherHistory), Close,
            RowBreak, Grp(), Land, RowBreak, Grp(),
            ContinuationValue(history), Sp, Eq, Sp, ContinuationValue(otherHistory), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
