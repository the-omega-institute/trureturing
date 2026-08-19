using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodic;

internal sealed class EnumerationSevenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var period = Id("p");
        var state = Id("s");
        var representatives = Id("tribonacciPeriodicOrbitRepresentativesSeven");
        var enumerated = Id("tribonacciEnumeratedOrbitStatesSeven");
        var partition = new Formula.Logic(
            Equal(Call("length", representatives), Num(25)),
            FormulaLogicOperator.And,
            Equal(Call("card", enumerated), Num(137)));
        var periodBounds = new Formula.Logic(
            new Formula.Relation(period, FormulaRelationOperator.GreaterThanOrEqual, Num(1)),
            FormulaLogicOperator.And,
            new Formula.Relation(period, FormulaRelationOperator.LessThanOrEqual, Num(7)));
        var periodic = Equal(
            Call("iterate", Id("tribonacciPeriodicTransition"), period, state),
            state);
        var complete = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("p"), Id("N")),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("s"),
                    Id("TribonacciPeriodicState")),
            ],
            new Formula.Logic(
                new Formula.Logic(periodBounds, FormulaLogicOperator.And, periodic),
                FormulaLogicOperator.Implies,
                new Formula.Relation(
                    state,
                    FormulaRelationOperator.MemberOf,
                    Id("decodedRepresentativeOrbitUnionSeven"))));
        var maximin = Call(
            "IsGreatest",
            Id("tribonacciPeriodicOrbitMinimaSeven"),
            Call("championValue", Id("t")));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The complete Tribonacci periodic enumeration through seven has unchanged "
                + "champion maximin.",
            H("Tribonacci Periodic Enumeration Through Seven"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("twenty-five-cycles-and-one-hundred-thirty-seven-phases"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSeven."
                            + "tribonacci_periodic_code_partition_seven"),
                    H("Twenty-five cycles and one hundred thirty-seven phase states"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(partition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Ten primitive seven-cycles add seventy phases to the prior fifteen "
                            + "cycles and sixty-seven phases."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("periodic-enumeration-through-seven-is-complete"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSeven."
                            + "tribonacci_periodic_orbit_enumeration_complete_seven"),
                    H("The enumeration through seven is complete"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(complete)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every real branch state fixed by a nonzero iterate of period at most "
                            + "seven occurs on one of the twenty-five decoded cycles."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("periodic-maximin-through-seven-is-unchanged"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSeven."
                            + "tribonacci_periodic_orbit_maximin_seven"),
                    H("The periodic maximin through seven is unchanged"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(maximin)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Each new cycle has a certified low arm below championValue(t), while "
                            + "the repeating ba orbit continues to attain equality."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodic/EnumerationSevenMaximinA")),
            ]));
    }
}
