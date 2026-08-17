using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodic;

internal sealed class EnumerationElevenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var period = Id("p");
        var state = Id("s");
        var representatives = Id("goldenPeriodicOrbitRepresentativesEleven");
        var pointCodes = Id("goldenPeriodicPointCodesEleven");
        var minima = Id("goldenPeriodicOrbitMinimaEleven");
        var pointCount = Equal(Call("card", pointCodes), Num(480));
        var orbitPartition = new Formula.Logic(
            Equal(Call("length", representatives), Num(54)),
            FormulaLogicOperator.And,
            Equal(Call("card", Id("goldenEnumeratedOrbitStatesEleven")), Num(480)));
        var periodBounds = new Formula.Logic(
            new Formula.Relation(period, FormulaRelationOperator.GreaterThanOrEqual, Num(1)),
            FormulaLogicOperator.And,
            new Formula.Relation(period, FormulaRelationOperator.LessThanOrEqual, Num(11)));
        var periodic = Equal(Call("iterate", Id("goldenTransition"), period, state), state);
        var complete = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("p"), Id("N")),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("s"), Id("GoldenSurvivorState")),
            ],
            new Formula.Logic(
                new Formula.Logic(periodBounds, FormulaLogicOperator.And, periodic),
                FormulaLogicOperator.Implies,
                new Formula.Relation(
                    state,
                    FormulaRelationOperator.MemberOf,
                    Id("decodedRepresentativeOrbitUnionEleven"))));
        var maximin = Call("IsGreatest", minima, Id("goldenThreshold"));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The exact golden periodic enumeration is complete through period eleven.",
            H("Golden Periodic Enumeration Through Eleven"),
            Blocks(
                Paragraph(Text(
                    "The period-ten certificate and eighteen primitive eleven-cycles are "
                        + "combined through a 199-equation exact fixed-point census.")),
                Describe.Lean(
                    DescribeId.Create("four-hundred-eighty-periodic-points-through-eleven"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationEleven."
                            + "golden_periodic_point_code_count_eleven"),
                    H("Four hundred eighty periodic points through eleven"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(pointCount)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The eighteen primitive eleven-cycles add 198 phases to the 282 phases "
                            + "enumerated through period ten."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("fifty-four-disjoint-periodic-orbits-through-eleven"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationEleven."
                            + "golden_periodic_code_partition_eleven"),
                    H("Fifty-four disjoint periodic orbits"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(orbitPartition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The 36 prior cycles and eighteen primitive eleven-cycles have no "
                            + "repeated exact phase code."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("periodic-orbit-enumeration-through-eleven-is-complete"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationEleven."
                            + "golden_periodic_orbit_enumeration_complete_eleven"),
                    H("The enumeration through period eleven is complete"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(complete)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every real state fixed by a nonzero iterate of period at most eleven "
                            + "lies on one of the fifty-four decoded exact cycles."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-periodic-maximin-through-eleven"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationEleven."
                            + "golden_periodic_orbit_maximin_eleven"),
                    H("The golden periodic maximin through eleven"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(maximin)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every new low-arm witness is bounded by the threshold, and the "
                            + "period-three champion continues to attain equality."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenPeriodic/EnumerationElevenFixed")),
            ]));
    }
}
