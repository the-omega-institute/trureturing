using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacciGeneral;

internal sealed class TribonacciPeriodicEnumerationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var representatives = Id("tribonacciPeriodicOrbitRepresentativesFive");
        var fixedPointCounts = Equal(
            Call("fixedPointEquationCountsThrough", Num(5)),
            Call("list", Num(1), Num(3), Num(7), Num(11), Num(21)));
        var periodDistribution = Equal(
            Call("orbitPeriodList", representatives),
            Call(
                "list",
                Num(1), Num(2), Num(3), Num(3), Num(4), Num(4),
                Num(5), Num(5), Num(5), Num(5)));
        var representativesValid = Call(
            "Forall",
            representatives,
            Id("tribonacciCodedOrbitValid"));
        var stateCodesNodup = Call(
            "Nodup",
            Call("flatMapOrbitStates", representatives));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact computation supplies ten valid, disjoint Tribonacci cycles through period five.",
            H("Tribonacci Periodic Enumeration"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("fixed-point-equation-counts-through-five"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration."
                            + "tribonacci_fixed_point_counts_through_five"),
                    H("Fixed-point equation counts through period five"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(fixedPointCounts)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The closed-walk generator produces 1, 3, 7, 11, and 21 phase-marked "
                            + "fixed-point equations at periods one through five."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("ten-orbit-period-distribution"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration."
                            + "tribonacci_periodic_orbit_period_distribution_five"),
                    H("The ten orbit periods are explicit"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(periodDistribution)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "There is one primitive cycle of periods one and two, two cycles of "
                            + "periods three and four, and four cycles of period five."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("all-representative-branches-are-valid"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration."
                            + "tribonacci_periodic_orbit_representatives_valid"),
                    H("Every representative uses valid branches"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(representativesValid)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Exact cubic inequalities certify the source gap, branch side, target "
                            + "gap, and closure condition for every displayed representative."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("coded-phase-states-are-globally-disjoint"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration."
                            + "tribonacci_periodic_orbit_state_codes_nodup"),
                    H("Coded phase states are globally disjoint"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(stateCodesNodup)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Flattening all ten cycles gives a list with no repeated exact cubic "
                            + "state code, including across different representatives."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicGenerator")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacciGeneral/ChampionValue")),
            ]));
    }
}
