using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValueScale;

internal sealed class OptimalFiberAlignmentUnderdeterminationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DecisionValueScale/OptimalFiberAlignmentUnderdetermination."
            + "proxy_optimal_tie_precludes_principal_guarantee";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unequal principal values within one proxy-optimal fiber preclude a principal-best "
            + "selection guarantee.",
        H("Optimal-Fiber Alignment Underdetermination"),
        Blocks(Describe.Lean(
            DescribeId.Create("proxy-optimal-tie-precludes-principal-guarantee"),
            DeclarationHandle.Create(Declaration),
            H("A proxy-optimal tie precludes a principal-best guarantee"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The two objectives are real-valued on the same feasible carrier. The first "
                        + "state is globally proxy-optimal, and the proxy tie makes the second "
                        + "state globally proxy-optimal as well.")),
                Paragraph(Text(
                    "If every proxy-maximizing selection were principal-best among all proxy "
                        + "maximizers, selecting each tied state in turn would force the two "
                        + "principal values to be equal, contradicting the source witness.")),
                Paragraph(Text(
                    "The source's subsequent three-part alignment prescription uses qualitative "
                        + "terms without in-scope predicates and is commentary outside the named "
                        + "formal theorem."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessThanOrEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Maximal(
        Formula carrier,
        Formula objective,
        Formula candidate,
        string comparisonName) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound(comparisonName, carrier)],
            LessThanOrEqualTo(
                Apply(objective, F.Id(comparisonName)),
                Apply(objective, candidate)));

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("Z");
        Formula agent = F.Id("agentObjective");
        Formula principal = F.Id("principalObjective");
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula selected = F.Id("selected");
        Formula alternative = F.Id("alternative");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula objectiveType = new Formula.TypeArrow(carrier, reals);

        Formula premises = And(
            EqualTo(Apply(agent, first), Apply(agent, second)),
            And(
                Maximal(carrier, agent, first, "candidate"),
                NotEqualTo(Apply(principal, first), Apply(principal, second))));

        Formula guarantee = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("selected", carrier)],
            Implies(
                Maximal(carrier, agent, selected, "candidate"),
                new Formula.BindMany(
                    FormulaQuantifier.ForAll,
                    [Bound("alternative", carrier)],
                    Implies(
                        Maximal(carrier, agent, alternative, "candidate"),
                        LessThanOrEqualTo(
                            Apply(principal, alternative),
                            Apply(principal, selected))))));

        Formula theorem = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Z", F.Id("Type")),
                Bound("agentObjective", objectiveType),
                Bound("principalObjective", objectiveType),
                Bound("first", carrier),
                Bound("second", carrier),
            ],
            Implies(premises, new Formula.Not(guarantee)));

        return Disp(theorem);
    }
}
