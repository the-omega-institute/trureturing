using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SufficiencyQuotient;

internal sealed class StrategyProfileQuotientMinimalityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/SufficiencyQuotient/StrategyProfileQuotientMinimality."
            + "strategy_sufficient_self_universal_minimality";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every strategy-sufficient history interface maps uniquely onto the complete "
            + "strategy-profile quotient.",
        H("Strategy Profile Quotient Minimality"),
        Blocks(Describe.Lean(
            DescribeId.Create("strategy-profile-quotient-minimality"),
            DeclarationHandle.Create(Declaration),
            H("The strategy-profile quotient is the coarsest sufficient history interface"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Histories, future input words, actions, and summary values are arbitrary "
                        + "types. A complete strategy profile assigns a probability mass "
                        + "function on actions to each history and future word.")),
                Paragraph(Text(
                    "The public premise supplies a predictor through the summary. The target "
                        + "is the named quotient by equality of complete strategy profiles, "
                        + "not an independently declared image or self-state carrier.")),
                Paragraph(Text(
                    "The unique factor starts on the realized range of the summary and sends "
                        + "every represented history to its canonical quotient class. This "
                        + "equation states both representative independence and the required "
                        + "factorization on the effective interface.")),
                Paragraph(Text(
                    "The proof instantiates the frozen minimal prediction-quotient theorem "
                        + "with the canonical joint readout. Pinned-library range "
                        + "factorization surjectivity then proves uniqueness directly."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula historyType = F.Id("History");
        Formula futureWordType = F.Id("FutureWord");
        Formula actionType = F.Id("Action");
        Formula summaryType = F.Id("Summary");
        Formula profile = F.Id("strategyProfile");
        Formula summary = F.Id("summary");
        Formula predictor = F.Id("predictor");
        Formula factor = F.Id("factor");
        Formula history = F.Id("h");
        Formula actionLaw = Call("PMF", actionType);
        Formula profileType = Arrow(
            historyType, Arrow(futureWordType, actionLaw));
        Formula quotient = Call("Quotient", Call("ker", profile));
        Formula summaryImage = Call("range", summary);
        Formula sufficient = EqualTo(
            profile, Call("compose", predictor, summary));
        Formula factorAtHistory = EqualTo(
            Call("quotientClass", profile, history),
            Apply(factor, Call("rangeFactorization", summary, history)));
        Formula factorLaw = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("h", historyType)],
            factorAtHistory);
        Formula uniqueFactor = Seq(
            Exists, Bang, Sp, factor, Colon, Sp,
            Arrow(summaryImage, quotient), Comma, Sp, factorLaw);
        Formula theorem = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("History", type),
                Bound("FutureWord", type),
                Bound("Action", type),
                Bound("Summary", type),
                Bound("strategyProfile", profileType),
                Bound("summary", Arrow(historyType, summaryType)),
                Bound("predictor", Arrow(summaryType, Arrow(futureWordType, actionLaw))),
            ],
            Implies(sufficient, uniqueFactor));

        return Disp(theorem);
    }
}
