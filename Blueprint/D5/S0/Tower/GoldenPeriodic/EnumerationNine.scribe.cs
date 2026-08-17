using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodic;

internal sealed class EnumerationNineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var period = Id("p");
        var state = Id("s");
        var naturals = Id("N");
        var states = Id("GoldenSurvivorState");
        var threshold = Id("goldenThreshold");
        var representatives = Id("goldenPeriodicOrbitRepresentativesNine");
        var pointCodes = Id("goldenPeriodicPointCodesNine");
        var minima = Id("goldenPeriodicOrbitMinimaNine");

        Formula Member(Formula value, Formula set) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

        var pointCount = Equal(Call("card", pointCodes), Num(172));
        var orbitPartition = new Formula.Logic(
            Equal(Call("length", representatives), Num(25)),
            FormulaLogicOperator.And,
            Equal(Call("card", Id("goldenEnumeratedOrbitStatesNine")), Num(172)));
        var periodBounds = new Formula.Logic(
            new Formula.Relation(period, FormulaRelationOperator.GreaterThanOrEqual, Num(1)),
            FormulaLogicOperator.And,
            new Formula.Relation(period, FormulaRelationOperator.LessThanOrEqual, Num(9)));
        var periodic = Equal(
            Call("iterate", Id("goldenTransition"), period, state),
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
                Member(state, Id("decodedRepresentativeOrbitUnionNine"))));
        var maximin = Call("IsGreatest", minima, threshold);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The exact golden periodic enumeration is complete through period nine.",
            H("Golden Periodic Enumeration Through Nine"),
            Blocks(
                Paragraph(Text(
                    "The period-eight theorem and eight new primitive period-nine cycles are "
                        + "combined without expanding one monolithic arithmetic proof. A first- "
                        + "and second-step partition keeps the finite comparisons bounded.")),
                Describe.Lean(
                    DescribeId.Create("one-hundred-seventy-two-periodic-points-through-nine"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationNine."
                            + "golden_periodic_point_code_count_nine"),
                    H("One hundred seventy-two periodic points through period nine"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(pointCount)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The eight primitive nine-cycles contribute seventy-two new phase states "
                            + "to the one hundred states known through period eight."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("twenty-five-disjoint-periodic-orbits-through-nine"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationNine."
                            + "golden_periodic_code_partition_nine"),
                    H("Twenty-five disjoint periodic orbits"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(orbitPartition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The exact state table splits without repetition into seventeen prior "
                            + "cycles and eight primitive cycles of length nine."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("periodic-orbit-enumeration-through-nine-is-complete"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationNine."
                            + "golden_periodic_orbit_enumeration_complete_nine"),
                    H("The enumeration through period nine is complete"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(complete)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every real state fixed by a nonzero iterate of period at most nine "
                            + "occurs on one of the twenty-five decoded exact cycles."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-periodic-maximin-through-nine"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationNine."
                            + "golden_periodic_orbit_maximin_nine"),
                    H("The golden periodic maximin through nine"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(maximin)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "All new cycles stay below the exact threshold, while the inherited "
                            + "period-three champion continues to attain equality."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenPeriodic/EnumerationNineData")),
            ]));
    }
}
