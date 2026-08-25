using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SufficiencyQuotient;

internal sealed class MinimalPredictionBeliefStateDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/SufficiencyQuotient/MinimalPredictionBeliefState."
            + "minimal_prediction_belief_state";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every summary sufficient for all future observation profiles maps uniquely "
            + "and surjectively onto the predictive belief quotient.",
        H("Minimal Prediction Belief State"),
        Blocks(Describe.Lean(
            DescribeId.Create("minimal-prediction-belief-state"),
            DeclarationHandle.Create(Declaration),
            H("The predictive quotient is the minimal empirical history state"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The carrier is an arbitrary history type with a dependent family of "
                        + "possible-observation readouts indexed by every future query. The "
                        + "canonical jointReadout forms the complete predictive profile; no "
                        + "second profile primitive is introduced.")),
                Paragraph(Text(
                    "A predictor through the summary is the public sufficiency premise. "
                        + "Equal summary values therefore give equal kernel-quotient classes "
                        + "and equal values for every empirical objective computed from the "
                        + "complete observation profile.")),
                Paragraph(Text(
                    "The factor starts at the realized image of the possibly redundant "
                        + "summary and ends at the named quotient by predictive equivalence. "
                        + "Its public factorization, surjectivity, and uniqueness express the "
                        + "minimality distinction from raw history and redundant summaries.")),
                Paragraph(Text(
                    "The proof applies the frozen causal-state image factorization and the "
                        + "pinned-library quotient-kernel equivalence. No exact existing "
                        + "theorem included the quotient, objective, and unrestricted empty-"
                        + "history clauses together."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula historyType = F.Id("History");
        Formula queryType = F.Id("Query");
        Formula summaryType = F.Id("Summary");
        Formula observation = F.Id("Observation");
        Formula possible = F.Id("possibleObservation");
        Formula summary = F.Id("summary");
        Formula predictor = F.Id("predictor");
        Formula joint = Call("jointReadout", possible);
        Formula profileType = Seq(
            Forall, Sp, F.Id("q"), Colon, Sp, queryType, Comma, Sp,
            Apply(observation, F.Id("q")));
        Formula possibleType = Seq(
            Forall, Sp, F.Id("q"), Colon, Sp, queryType, Comma, Sp,
            historyType, Sp, To, Sp, Apply(observation, F.Id("q")));
        Formula belief = Call("Quotient", Call("ker", joint));
        Formula summaryImage = Call("range", summary);
        Formula history = F.Id("h");
        Formula historyPrime = F.Id("hPrime");
        Formula objectiveType = F.Id("Objective");
        Formula objective = F.Id("g");
        Formula factor = F.Id("factor");

        Formula sufficient = EqualTo(
            joint, Call("compose", predictor, summary));
        Formula sameSummary = EqualTo(
            Apply(summary, history), Apply(summary, historyPrime));
        Formula sameBelief = EqualTo(
            Call("quotientClass", joint, history),
            Call("quotientClass", joint, historyPrime));
        Formula allObjectives = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("Objective", type), Bound("g", Arrow(profileType, objectiveType))],
            EqualTo(
                Apply(objective, Apply(joint, history)),
                Apply(objective, Apply(joint, historyPrime))));
        Formula equalSummariesDetermine = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("h", historyType), Bound("hPrime", historyType)],
            Implies(sameSummary, And(sameBelief, allObjectives)));
        Formula factorLaw = And(
            EqualTo(Call("quotientClassMap", joint),
                Call("compose", factor, Call("rangeFactorization", summary))),
            Call("Surjective", factor));
        Formula uniqueFactor = Seq(
            Exists, Bang, Sp, factor, Colon, Sp,
            Arrow(summaryImage, belief), Comma, Sp, factorLaw);
        Formula conclusion = And(equalSummariesDetermine, uniqueFactor);
        Formula theorem = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("History", type), Bound("Query", type), Bound("Summary", type),
                Bound("Observation", Arrow(queryType, type)),
                Bound("possibleObservation", possibleType),
                Bound("summary", Arrow(historyType, summaryType)),
                Bound("predictor", Arrow(summaryType, profileType)),
            ],
            Implies(sufficient, conclusion));

        return Disp(theorem);
    }
}
