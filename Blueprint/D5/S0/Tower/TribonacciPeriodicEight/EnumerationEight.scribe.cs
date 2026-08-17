using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicEight;

internal sealed class EnumerationEightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var period = Id("p");
        var state = Id("s");
        var representatives = Id("tribonacciPeriodicOrbitRepresentativesEight");
        var phases = Id("tribonacciPeriodicOrbitPhaseCertificatesEight");
        var partition = new Formula.Logic(
            Equal(Call("length", representatives), Num(40)),
            FormulaLogicOperator.And,
            Equal(Call("length", phases), Num(257)));
        var periodBounds = new Formula.Logic(
            new Formula.Relation(period, FormulaRelationOperator.GreaterThanOrEqual, Num(1)),
            FormulaLogicOperator.And,
            new Formula.Relation(period, FormulaRelationOperator.LessThanOrEqual, Num(8)));
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
                    Id("decodedRepresentativeOrbitUnionEight"))));
        var maximin = Call(
            "IsGreatest",
            Id("tribonacciPeriodicOrbitMinimaEight"),
            Call("championValue", Id("t")));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The complete Tribonacci periodic enumeration through eight has unchanged champion maximin.",
            H("Tribonacci Periodic Enumeration Through Eight"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("forty-cycles-and-two-hundred-fifty-seven-phases"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEight."
                            + "tribonacci_periodic_code_partition_eight"),
                    H("Forty cycles and two hundred fifty-seven phase certificates"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(partition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Fifteen primitive eight-cycles add one hundred twenty phases to the "
                            + "prior twenty-five cycles and one hundred thirty-seven phases."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("periodic-enumeration-through-eight-is-complete"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEight."
                            + "tribonacci_periodic_orbit_enumeration_complete_eight"),
                    H("The enumeration through eight is complete"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(complete)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every real branch state fixed by a nonzero iterate of period at most "
                            + "eight occurs on one of the forty decoded cycles."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("periodic-maximin-through-eight-is-unchanged"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEight."
                            + "tribonacci_periodic_orbit_maximin_eight"),
                    H("The periodic maximin through eight is unchanged"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(maximin)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Each new cycle has a certified low arm below championValue(t), while "
                            + "the repeating ba orbit continues to attain equality."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightMaximinA")),
            ]));
    }
}
