using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class PosteriorStoppingMapErrorBoundDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/DecisionRisk/PosteriorStoppingMapErrorBound."
            + "posterior_stopping_map_error_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A posterior-maximizing decision made at the stopping threshold has total "
            + "error at most that threshold.",
        H("Posterior Stopping MAP Error Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("posterior-stopping-map-error-bound"),
                DeclarationHandle.Create(Declaration),
                H("MAP output at the posterior threshold controls total error"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The stopped-history law is a PMF on an arbitrary history carrier. "
                            + "Each history has a PMF posterior on the finite state space, so "
                            + "their product constructs the stopped joint law directly.")),
                    Paragraph(Text(
                        "The stopping clause supplies a posterior maximizer with residual "
                            + "mass at most epsilon. The reported state is independently "
                            + "required to maximize the same posterior, hence it has that "
                            + "same residual conditional error.")),
                    Paragraph(Text(
                        "Summing the conditional error against the normalized history law "
                            + "gives the displayed joint probability of reporting a state "
                            + "different from the true state."))),
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
        Formula stateType = F.Id("X");
        Formula historyType = F.Id("H");
        Formula historyLaw = F.Id("mu");
        Formula posterior = F.Id("pi");
        Formula estimate = F.Id("xHat");
        Formula epsilon = F.Id("epsilon");
        Formula history = F.Id("h");
        Formula state = F.Id("x");
        Formula mapState = F.Id("xStar");
        Formula ennreal = F.Id("ENNReal");
        Formula Estimate(Formula h) => Apply(estimate, h);
        Formula Posterior(Formula h, Formula x) => Apply(Apply(posterior, h), x);
        Formula maximalAtEstimate = Seq(
            Forall, Sp, history, Comma, Sp, state, Comma, Sp,
            Posterior(history, state), Sp, Leq, Sp,
            Posterior(history, Estimate(history)));
        Formula stoppingClause = Seq(
            Forall, Sp, history, Comma, Sp, Exists, Sp, mapState, Comma, Sp,
            Open,
            Forall, Sp, state, Comma, Sp,
            Posterior(history, state), Sp, Leq, Sp,
            Posterior(history, mapState), Close,
            Sp, Land, Sp,
            D(1), Sp, Minus, Sp, Posterior(history, mapState),
            Sp, Leq, Sp, epsilon);
        Formula conditionalError = Call("tsum", state, Seq(
            OpenBracket, Estimate(history), Sp, Neq, Sp, state, CloseBracket,
            Sp, Posterior(history, state)));
        Formula totalError = Call("tsum", history, Seq(
            Apply(historyLaw, history), Sp, Cdot, Sp, conditionalError));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, historyType, Comma, RowBreak, Grp(),
            Call("Finite", stateType), Comma, Sp,
            Call("DecidableEq", stateType), Comma, RowBreak, Grp(),
            historyLaw, Colon, Sp, Call("PMF", historyType), Comma, RowBreak, Grp(),
            posterior, Colon, Sp, historyType, Sp, To, Sp,
            Call("PMF", stateType), Comma, RowBreak, Grp(),
            estimate, Colon, Sp, historyType, Sp, To, Sp, stateType,
            Comma, Sp, epsilon, Colon, Sp, ennreal, Comma, RowBreak, Grp(),
            Open, maximalAtEstimate, Close, Sp, Land, RowBreak, Grp(),
            Open, stoppingClause, Close, Sp, Rightarrow, RowBreak, Grp(),
            totalError, Sp, Leq, Sp, epsilon, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
