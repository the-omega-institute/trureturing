using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodic;

internal sealed class EnumerationEightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var period = Id("p");
        var state = Id("s");
        var naturals = Id("N");
        var states = Id("GoldenSurvivorState");
        var threshold = Id("goldenThreshold");
        var representatives = Id("goldenPeriodicOrbitRepresentativesEight");
        var pointCodes = Id("goldenPeriodicPointCodesEight");
        var minima = Id("goldenPeriodicOrbitMinimaEight");

        Formula Member(Formula value, Formula set) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

        var pointCount = Equal(Call("card", pointCodes), Num(100));
        var orbitPartition = new Formula.Logic(
            Equal(Call("length", representatives), Num(17)),
            FormulaLogicOperator.And,
            Equal(Call("card", Id("goldenEnumeratedOrbitStatesEight")), Num(100)));
        var periodBounds = new Formula.Logic(
            new Formula.Relation(period, FormulaRelationOperator.GreaterThanOrEqual, Num(1)),
            FormulaLogicOperator.And,
            new Formula.Relation(period, FormulaRelationOperator.LessThanOrEqual, Num(8)));
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
                Member(state, Id("decodedRepresentativeOrbitUnionEight"))));
        var maximin = Call("IsGreatest", minima, threshold);

        return DocumentDefinition.Create(ScribeNode.Create(
            "One incremental exact certificate extends the golden periodic enumeration through period eight.",
            H("Golden Periodic Enumeration Through Eight"),
            Blocks(
                Paragraph(Text(
                    "The frozen period-at-most-seven certificate is reused without expansion. "
                        + "Only period-eight branch words are solved over Q(phi), then split by "
                        + "their first transition so each finite check remains bounded.")),
                Describe.Lean(
                    DescribeId.Create("one-hundred-periodic-points-through-period-eight"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationEight."
                            + "golden_periodic_point_code_count_eight"),
                    H("One hundred periodic points through period eight"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(pointCount)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The five new primitive period-eight cycles contribute forty new phase "
                            + "states; together with the frozen sixty states this gives one hundred."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("seventeen-disjoint-periodic-orbits-through-eight"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationEight."
                            + "golden_periodic_code_partition_eight"),
                    H("Seventeen disjoint periodic orbits"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(orbitPartition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The one hundred exact state codes split without repetition into the "
                            + "twelve frozen cycles and five primitive cycles of length eight."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("periodic-orbit-enumeration-through-eight-is-complete"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationEight."
                            + "golden_periodic_orbit_enumeration_complete_eight"),
                    H("The enumeration through period eight is complete"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(complete)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every real state fixed by a nonzero iterate of period at most eight "
                            + "occurs on one of the seventeen decoded exact cycles."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-periodic-maximin-through-eight"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationEight."
                            + "golden_periodic_orbit_maximin_eight"),
                    H("The golden periodic maximin through eight"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(maximin)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Each new cycle has a certified low state whose arm is at most phi "
                            + "inverse squared over two, while the frozen period-three cycle "
                            + "continues to attain equality."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Champions/GoldenPeriodicEnumeration")),
            ]));
    }
}
