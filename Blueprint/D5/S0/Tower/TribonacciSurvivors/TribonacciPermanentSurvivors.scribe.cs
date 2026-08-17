using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciSurvivors;

internal sealed class TribonacciPermanentSurvivorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var n = Id("n");
        var state = Id("s");
        var naturals = Id("N");
        var states = Id("TribonacciPeriodicState");
        var strictSet = Id("tribonacciStrictSurvivorSet");
        var closedSet = Id("tribonacciClosedSurvivorSet");

        Formula Backward(Formula set, Formula depth) =>
            Call("tribonacciBackwardSurvivor", set, depth);

        Formula Member(Formula value, Formula set) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

        Formula Permanent(Formula value, Formula set) => new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            naturals,
            Member(value, Backward(set, n)));

        var strictPermanentSetEmpty = Equal(
            Id("tribonacciStrictPermanentSet"),
            Id("emptySet"));

        var strictDomainNonempty = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("s"),
            states,
            Member(state, strictSet));

        var closedChampionCarrier = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("s"),
            states,
            new Formula.Logic(
                Call("IsTribonacciClosedChampionState", state),
                FormulaLogicOperator.Implies,
                Permanent(state, closedSet)));

        const string declarationPrefix =
            "D5/S0/Tower/TribonacciSurvivors/TribonacciPermanentSurvivors.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Strict Tribonacci permanent survival is empty, while the strict one-step domain "
                + "and a closed period-two permanent carrier are nonempty.",
            H("Tribonacci Permanent Survivors"),
            Blocks(
                Paragraph(Text(
                    "The deterministic three-gap map is expanding. A permanently strict state "
                        + "must enter the large-to-combined two-step branch. Backward comparison "
                        + "with the reciprocal-square contraction then forces the unique boundary "
                        + "period-two orbit, whose large phase is excluded by the strict threshold.")),
                Describe.Lean(
                    DescribeId.Create("strict-tribonacci-permanent-survivor-set-is-empty"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacci_strict_permanent_set_eq_empty"),
                    H("The strict permanent survivor set is empty"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(strictPermanentSetEmpty)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This is an all-depth intersection statement: no state survives every "
                            + "finite backward depth. It does not assert that the finite-depth "
                            + "survivor at depth 60 is empty."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("strict-tribonacci-one-step-domain-is-nonempty"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacci_strict_survivor_set_nonempty"),
                    H("The strict one-step survivor domain is nonempty"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(strictDomainNonempty)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The combined-gap midpoint lies strictly above the threshold. Permanent "
                            + "emptiness is therefore not a vacuous consequence of an empty "
                            + "initial domain."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("closed-tribonacci-champion-carrier-survives"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacci_closed_champion_carrier_subset"),
                    H("The closed champion carrier survives permanently"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(closedChampionCarrier)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The large and combined champion states form a closed period-two orbit. "
                            + "Their inclusion is a proved lower bound for the closed permanent "
                            + "set, not a classification or an equality."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin")),
            ]));
    }
}
