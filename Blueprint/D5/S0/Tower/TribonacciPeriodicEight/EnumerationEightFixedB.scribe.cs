using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicEight;

internal sealed class EnumerationEightFixedBDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var lastStates = Id("tribonacciPeriodEightLastPhaseStates");
        var equations = Id("tribonacciPeriodEightFixedPointCodes");
        var subset = new Formula.Relation(
            lastStates,
            FormulaRelationOperator.SubsetOf,
            equations);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The final five primitive cycles occur among the period-eight equations.",
            H("Tribonacci Period-Eight Equation Identifications"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("last-five-cycles-occur-in-period-eight-equations"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightFixedB."
                            + "tribonacci_last_new_orbit_states_subset_fixed_points_eight"),
                    H("The final five cycles occur in the equation set"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(subset)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Explicit closed rotations identify each phase without re-expanding the "
                            + "complete one hundred thirty-one-equation system."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightFixedBase")),
            ]));
    }
}
