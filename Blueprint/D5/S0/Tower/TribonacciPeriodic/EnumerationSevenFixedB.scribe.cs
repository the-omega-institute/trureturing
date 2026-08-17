using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodic;

internal sealed class EnumerationSevenFixedBDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var lastStates = Id("tribonacciPeriodSevenLastPhaseStates");
        var equations = Id("tribonacciPeriodSevenFixedPointCodes");
        var subset = new Formula.Relation(
            lastStates,
            FormulaRelationOperator.SubsetOf,
            equations);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The second five new cycles occur among the period-seven equations.",
            H("Second Tribonacci Period-Seven Equation Identifications"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("last-five-cycles-occur-in-period-seven-equations"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSevenFixedB."
                            + "tribonacci_last_new_orbit_states_subset_fixed_points_seven"),
                    H("The second five cycles occur in the equation set"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(subset)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Rotated itinerary witnesses avoid re-expanding the complete "
                            + "seventy-one-equation system for each orbit."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodic/EnumerationSevenFixedBase")),
            ]));
    }
}
