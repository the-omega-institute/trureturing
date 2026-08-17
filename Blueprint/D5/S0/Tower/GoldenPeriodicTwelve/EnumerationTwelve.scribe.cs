using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodicTwelve;

internal sealed class EnumerationTwelveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var period = Id("p");
        var state = Id("s");
        var representatives = Id("goldenPeriodicOrbitRepresentativesTwelve");
        var pointCodes = Id("goldenPeriodicPointCodesTwelve");
        var minima = Id("goldenPeriodicOrbitMinimaTwelve");
        var pointCount = Equal(Call("card", pointCodes), Num(780));
        var orbitPartition = new Formula.Logic(
            Equal(Call("length", representatives), Num(79)),
            FormulaLogicOperator.And,
            Equal(Call("card", Id("goldenEnumeratedOrbitStatesTwelve")), Num(780)));
        var periodBounds = new Formula.Logic(
            new Formula.Relation(period, FormulaRelationOperator.GreaterThanOrEqual, Num(1)),
            FormulaLogicOperator.And,
            new Formula.Relation(period, FormulaRelationOperator.LessThanOrEqual, Num(12)));
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
                    Id("decodedRepresentativeOrbitUnionTwelve"))));
        var maximin = Call("IsGreatest", minima, Id("goldenThreshold"));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The exact golden periodic enumeration is complete through period twelve.",
            H("Golden Periodic Enumeration Through Twelve"),
            Blocks(
                Paragraph(Text(
                    "The period-eleven certificate and twenty-five primitive twelve-cycles "
                        + "are combined through a 322-equation exact fixed-point census.")),
                Describe.Lean(
                    DescribeId.Create("seven-hundred-eighty-periodic-points-through-twelve"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelve."
                            + "golden_periodic_point_code_count_twelve"),
                    H("Seven hundred eighty periodic points through twelve"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(pointCount)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The twenty-five primitive twelve-cycles add 300 phases to the 480 "
                            + "phases enumerated through period eleven."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("seventy-nine-disjoint-periodic-orbits-through-twelve"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelve."
                            + "golden_periodic_code_partition_twelve"),
                    H("Seventy-nine disjoint periodic orbits"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(orbitPartition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The 54 prior cycles and twenty-five primitive twelve-cycles have no "
                            + "repeated exact phase code."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("periodic-orbit-enumeration-through-twelve-is-complete"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelve."
                            + "golden_periodic_orbit_enumeration_complete_twelve"),
                    H("The enumeration through period twelve is complete"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(complete)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every real state fixed by a nonzero iterate of period at most twelve "
                            + "lies on one of the 79 decoded exact cycles."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-periodic-maximin-through-twelve"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelve."
                            + "golden_periodic_orbit_maximin_twelve"),
                    H("The golden periodic maximin through twelve"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(maximin)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every new low-arm witness is bounded by the threshold, and the "
                            + "period-three champion continues to attain equality."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveFixed")),
            ]));
    }
}
