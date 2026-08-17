using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodic;

internal sealed class EnumerationTenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var period = Id("p");
        var state = Id("s");
        var naturals = Id("N");
        var states = Id("GoldenSurvivorState");
        var threshold = Id("goldenThreshold");
        var representatives = Id("goldenPeriodicOrbitRepresentativesTen");
        var pointCodes = Id("goldenPeriodicPointCodesTen");
        var minima = Id("goldenPeriodicOrbitMinimaTen");

        Formula Member(Formula value, Formula set) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

        var pointCount = Equal(Call("card", pointCodes), Num(282));
        var orbitPartition = new Formula.Logic(
            Equal(Call("length", representatives), Num(36)),
            FormulaLogicOperator.And,
            Equal(Call("card", Id("goldenEnumeratedOrbitStatesTen")), Num(282)));
        var periodBounds = new Formula.Logic(
            new Formula.Relation(period, FormulaRelationOperator.GreaterThanOrEqual, Num(1)),
            FormulaLogicOperator.And,
            new Formula.Relation(period, FormulaRelationOperator.LessThanOrEqual, Num(10)));
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
                Member(state, Id("decodedRepresentativeOrbitUnionTen"))));
        var maximin = Call("IsGreatest", minima, threshold);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The exact golden periodic enumeration is complete through period ten.",
            H("Golden Periodic Enumeration Through Ten"),
            Blocks(
                Paragraph(Text(
                    "The period-nine theorem and eleven new primitive period-ten cycles are "
                        + "combined through an eight-block fixed-point decomposition.")),
                Describe.Lean(
                    DescribeId.Create("two-hundred-eighty-two-periodic-points-through-ten"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationTen."
                            + "golden_periodic_point_code_count_ten"),
                    H("Two hundred eighty-two periodic points through period ten"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(pointCount)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The eleven primitive ten-cycles contribute one hundred ten new phase "
                            + "states to the 172 states known through period nine."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("thirty-six-disjoint-periodic-orbits-through-ten"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationTen."
                            + "golden_periodic_code_partition_ten"),
                    H("Thirty-six disjoint periodic orbits"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(orbitPartition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The exact state table splits without repetition into twenty-five prior "
                            + "cycles and eleven primitive cycles of length ten."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("periodic-orbit-enumeration-through-ten-is-complete"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationTen."
                            + "golden_periodic_orbit_enumeration_complete_ten"),
                    H("The enumeration through period ten is complete"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(complete)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every real state fixed by a nonzero iterate of period at most ten "
                            + "occurs on one of the thirty-six decoded exact cycles."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-periodic-maximin-through-ten"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationTen."
                            + "golden_periodic_orbit_maximin_ten"),
                    H("The golden periodic maximin through ten"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(maximin)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "All new cycles stay below the exact threshold, while the inherited "
                            + "period-three champion continues to attain equality."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenPeriodic/EnumerationTenFixed")),
            ]));
    }
}
