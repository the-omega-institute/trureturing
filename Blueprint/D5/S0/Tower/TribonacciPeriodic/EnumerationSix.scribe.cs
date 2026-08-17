using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodic;

internal sealed class EnumerationSixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var period = Id("p");
        var state = Id("s");
        var representatives = Id("tribonacciPeriodicOrbitRepresentativesSix");
        var enumerated = Id("tribonacciEnumeratedOrbitStatesSix");
        var partition = new Formula.Logic(
            Equal(Call("length", representatives), Num(15)),
            FormulaLogicOperator.And,
            Equal(Call("card", enumerated), Num(67)));
        var periodBounds = new Formula.Logic(
            new Formula.Relation(period, FormulaRelationOperator.GreaterThanOrEqual, Num(1)),
            FormulaLogicOperator.And,
            new Formula.Relation(period, FormulaRelationOperator.LessThanOrEqual, Num(6)));
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
                    Id("decodedRepresentativeOrbitUnionSix"))));
        var maximin = Call(
            "IsGreatest",
            Id("tribonacciPeriodicOrbitMinimaSix"),
            Call("championValue", Id("t")));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The complete Tribonacci periodic enumeration through six has unchanged "
                + "champion maximin.",
            H("Tribonacci Periodic Enumeration Through Six"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("fifteen-cycles-and-sixty-seven-phase-states"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSix."
                            + "tribonacci_periodic_code_partition_six"),
                    H("Fifteen cycles and sixty-seven phase states"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(partition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Five primitive six-cycles add thirty phases to the prior ten cycles "
                            + "and thirty-seven phases."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("periodic-enumeration-through-six-is-complete"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSix."
                            + "tribonacci_periodic_orbit_enumeration_complete_six"),
                    H("The enumeration through six is complete"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(complete)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every real branch state fixed by a nonzero iterate of period at most "
                            + "six occurs on one of the fifteen decoded cycles."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("periodic-maximin-through-six-is-unchanged"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSix."
                            + "tribonacci_periodic_orbit_maximin_six"),
                    H("The periodic maximin through six is unchanged"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(maximin)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Each new cycle has a certified low arm below championValue(t), while "
                            + "the repeating ba orbit continues to attain equality."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodic/EnumerationSixFixed")),
            ]));
    }
}
