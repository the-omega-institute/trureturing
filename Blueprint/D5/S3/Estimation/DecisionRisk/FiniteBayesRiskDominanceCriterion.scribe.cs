using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class FiniteBayesRiskDominanceCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/DecisionRisk/FiniteBayesRiskDominanceCriterion."
            + "finite_bayes_risk_dominance_iff_postprocessing";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact randomized postprocessing between finite experiments is equivalent to "
            + "real Bayes-risk dominance for every finite decision problem.",
        H("Finite Bayes-Risk Dominance Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-bayes-risk-dominance-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Decision dominance characterizes finite postprocessing"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A source observation can simulate every target decision whenever a "
                        + "row-stochastic source-to-target kernel reproduces the target "
                        + "experiment. Composing that kernel with a target decision rule gives "
                        + "the corresponding source decision rule at the same real expected "
                        + "cost. The displayed risk is the real infimum of these costs, so "
                        + "negative losses are retained rather than truncated.")),
                Paragraph(Text(
                    "Conversely, the finite product of row simplexes is compact and convex. A "
                        + "target outside its simulated image has a strict linear separator; a "
                        + "uniform prior and shifted real loss turn that separator into a finite "
                        + "decision problem that reverses the asserted risk order."))),
            DescribeRole.Theorem))));

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

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("Theta");
        Formula sourceObservation = F.Id("X");
        Formula targetObservation = F.Id("Y");
        Formula action = F.Id("A");
        Formula source = F.Id("E");
        Formula target = F.Id("F");
        Formula simulator = F.Id("K");
        Formula prior = F.Id("pi");
        Formula loss = F.Id("ell");
        Formula decision = F.Id("d");
        Formula stateValue = F.Id("theta");
        Formula type = F.Id("Type");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));

        Formula postprocessing = Seq(
            Exists, Sp, simulator, Colon, Sp,
            Call("FiniteMarkovKernel", sourceObservation, targetObservation), Comma, Sp,
            target, Sp, Eq, Sp,
            Lambda(stateValue,
                Call("channelOutput", simulator, Apply(source, stateValue))));

        Formula normalizedPrior = Seq(
            Open, Forall, Sp, stateValue, Comma, Sp,
            D(0), Sp, Leq, Sp, Apply(prior, stateValue), Close,
            Sp, Land, Sp, Call("sum", prior), Sp, Eq, Sp, D(1));

        Formula RealBayesRisk(Formula experiment) => Call("sInf", Call("range",
            Lambda(decision, Call("finiteBayesCost", prior, loss, experiment, decision))));

        Formula universalRiskOrder = Seq(
            Forall, Sp, action, Colon, Sp, type, Comma, Sp,
            Call("Fintype", action), Comma, RowBreak, Grp(),
            prior, Colon, Sp, Arrow(state, real), Comma, Sp,
            loss, Colon, Sp, Arrow(state, Arrow(action, real)), Comma, RowBreak, Grp(),
            Grp(normalizedPrior), Sp, Rightarrow, RowBreak, Grp(),
            RealBayesRisk(source), Sp, Leq, Sp, RealBayesRisk(target));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, sourceObservation, Comma, Sp,
            targetObservation, Colon, Sp, type, Comma, RowBreak, Grp(),
            Call("Fintype", state), Sp, Land, Sp, Call("Nonempty", state), Sp,
            Land, Sp, Call("Fintype", sourceObservation), Sp, Land, Sp,
            Call("Fintype", targetObservation), Comma, RowBreak, Grp(),
            source, Colon, Sp, Arrow(state, Arrow(sourceObservation, real)), Comma, Sp,
            target, Colon, Sp, Arrow(state, Arrow(targetObservation, real)), Comma,
            RowBreak, Grp(),
            Call("IsRowStochastic", source), Sp, Land, Sp,
            Call("IsRowStochastic", target), Sp, Rightarrow, RowBreak, Grp(),
            Open, postprocessing, Close, Sp, Leftrightarrow, RowBreak, Grp(),
            Open, universalRiskOrder, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
