using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Champions;

internal sealed class GoldenPeriodicEnumerationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var period = Id("p");
        var state = Id("s");
        var naturals = Id("N");
        var states = Id("GoldenSurvivorState");
        var threshold = Id("goldenThreshold");
        var representatives = Id("goldenPeriodicOrbitRepresentativesSeven");
        var pointCodes = Id("goldenPeriodicPointCodesSeven");
        var minima = Id("goldenPeriodicOrbitMinimaSeven");

        Formula Member(Formula value, Formula set) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

        var pointCount = Equal(Call("card", pointCodes), Num(60));
        var orbitPartition = new Formula.Logic(
            Equal(Call("length", representatives), Num(12)),
            FormulaLogicOperator.And,
            Equal(Call("card", Id("goldenEnumeratedOrbitStatesSeven")), Num(60)));
        var periodBounds = new Formula.Logic(
            new Formula.Relation(period, FormulaRelationOperator.GreaterThanOrEqual, Num(1)),
            FormulaLogicOperator.And,
            new Formula.Relation(period, FormulaRelationOperator.LessThanOrEqual, Num(7)));
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
                Member(state, Id("decodedRepresentativeOrbitUnion"))));
        var maximin = Call("IsGreatest", minima, threshold);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact quadratic arithmetic freezes the complete golden periodic enumeration through period seven.",
            H("Golden Periodic Enumeration"),
            Blocks(
                Paragraph(Text(
                    "Each chart-compatible branch word is composed as an affine map over Q(phi). "
                        + "Its fixed-point equation is solved exactly, and the real branch word of "
                        + "any periodic state is sent back to that finite symbolic list.")),
                Describe.Lean(
                    DescribeId.Create("sixty-periodic-points-through-period-seven"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenPeriodicEnumeration."
                            + "golden_periodic_point_code_count_seven"),
                    H("Sixty periodic points through period seven"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(pointCount)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Deduplicating every exact fixed-point code from periods one through "
                            + "seven gives sixty points."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("twelve-disjoint-periodic-orbits"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenPeriodicEnumeration."
                            + "golden_periodic_code_partition_seven"),
                    H("Twelve disjoint periodic orbits"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(orbitPartition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The sixty codes split without repetition into twelve cycles: one each "
                            + "of lengths one through four, two each of lengths five and six, "
                            + "and four of length seven."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("periodic-orbit-enumeration-is-complete"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenPeriodicEnumeration."
                            + "golden_periodic_orbit_enumeration_complete"),
                    H("The periodic-orbit enumeration is complete"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(complete)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every nonzero period at most seven, any real state fixed by that "
                            + "iterate occurs on one of the twelve decoded cycles. This is the "
                            + "completeness half of the finite certificate."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-periodic-maximin-through-seven"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenPeriodicEnumeration."
                            + "golden_periodic_orbit_maximin_seven"),
                    H("The golden periodic maximin through seven"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(maximin)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every displayed cycle has an attained minimum arm and a selected state "
                            + "whose arm is at most phi inverse squared over two. The period-three "
                            + "cycle has all three arms at least that value and attains equality, "
                            + "so it is the greatest finite-orbit minimum."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Champions/GoldenSurvivorTubes")),
            ]));
    }
}
