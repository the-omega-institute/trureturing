using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacciGeneral;

internal sealed class TribonacciPeriodicCompletenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var period = Id("p");
        var state = Id("s");
        var naturals = Id("N");
        var states = Id("TribonacciPeriodicState");
        var representatives = Id("tribonacciPeriodicOrbitRepresentativesFive");
        var enumeratedStates = Id("tribonacciEnumeratedOrbitStatesFive");
        var pointCodes = Id("tribonacciPeriodicPointCodesFive");

        Formula Member(Formula value, Formula set) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

        var fixedPointEquality = Equal(enumeratedStates, pointCodes);
        var partition = new Formula.Logic(
            Equal(Call("length", representatives), Num(10)),
            FormulaLogicOperator.And,
            Equal(Call("card", enumeratedStates), Num(37)));
        var periodBounds = new Formula.Logic(
            new Formula.Relation(
                period,
                FormulaRelationOperator.GreaterThanOrEqual,
                Num(1)),
            FormulaLogicOperator.And,
            new Formula.Relation(
                period,
                FormulaRelationOperator.LessThanOrEqual,
                Num(5)));
        var periodic = Equal(
            Call("iterate", Id("tribonacciPeriodicTransition"), period, state),
            state);
        var complete = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("p"), naturals),
                new Formula.BoundVariable(FormulaIdentifier.Create("s"), states),
            ],
            new Formula.Logic(
                new Formula.Logic(periodBounds, FormulaLogicOperator.And, periodic),
                FormulaLogicOperator.Implies,
                Member(state, Id("decodedRepresentativeOrbitUnion"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Ten disjoint cycles exhaust every real Tribonacci periodic state through period five.",
            H("Tribonacci Periodic Completeness"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("orbit-states-equal-all-generated-fixed-points"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicCompleteness."
                            + "tribonacci_enumerated_orbit_states_eq_fixed_points"),
                    H("Orbit states equal all generated fixed points"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(fixedPointEquality)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Expanding every closed itinerary through period five shows that its "
                            + "fixed-point code occurs on one of the explicit cycles, and conversely."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("ten-cycles-partition-thirty-seven-states"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicCompleteness."
                            + "tribonacci_periodic_orbit_partition_five"),
                    H("Ten cycles partition thirty-seven phase states"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(partition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Global code distinctness converts the summed primitive periods into "
                            + "exactly thirty-seven different phase states."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("real-periodic-orbit-enumeration-is-complete"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicCompleteness."
                            + "tribonacci_periodic_orbit_enumeration_complete_five"),
                    H("The real periodic-orbit enumeration is complete"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(complete)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every nonzero period at most five, any real state fixed by that "
                            + "iterate lies on one of the ten decoded representative cycles."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration")),
            ]));
    }
}
