using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodic;

internal sealed class EnumerationNineDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var representatives = Id("goldenPeriodicOrbitRepresentativesExactlyNine");
        var valid = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("O"),
            representatives,
            Call("goldenCodedOrbitValid", Id("O")));
        var count = Equal(Call("length", representatives), Num(8));
        var nodup = Call(
            "Nodup",
            Call("flatMap", Id("goldenOrbitStates"), representatives));
        var lowBound = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("O"),
            representatives,
            new Formula.Relation(
                Call(
                    "goldenStateArm",
                    Call("decodeGoldenState", Call("lowState", Id("O")))),
                FormulaRelationOperator.LessThanOrEqual,
                Id("goldenThreshold")));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Eight exact primitive period-nine orbit certificates extend the golden data table.",
            H("Primitive Golden Period-Nine Certificates"),
            Blocks(
                Paragraph(Text(
                    "The period-nine branch words are solved exactly over Q(phi). Their closure, "
                        + "validity, separation from earlier periods, and low-arm witnesses are "
                        + "checked in bounded groups.")),
                Describe.Lean(
                    DescribeId.Create("eight-primitive-period-nine-orbits"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationNineData."
                            + "golden_new_periodic_orbit_count_nine"),
                    H("Eight primitive period-nine orbits"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(count)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The exact table contains eight representatives, each carrying a "
                            + "nine-step closed itinerary."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("period-nine-representatives-are-valid"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationNineData."
                            + "golden_new_periodic_orbit_representatives_valid_nine"),
                    H("The period-nine representatives are valid"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(valid)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every displayed code remains in the unit interval and follows the "
                            + "source, target, and affine rules of its branch word."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("seventy-two-new-state-codes-are-distinct"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationNineData."
                            + "golden_new_periodic_orbit_state_codes_nodup_nine"),
                    H("The seventy-two new state codes are distinct"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(nodup)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Flattening the eight nine-cycles produces no repeated exact state "
                            + "code."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("period-nine-low-arms-obey-the-golden-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationNineData."
                            + "golden_new_periodic_orbit_low_arms_bounded_nine"),
                    H("Period-nine low arms obey the golden bound"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(lowBound)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Each new cycle has an explicit member whose arm is at most the exact "
                            + "golden threshold."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenPeriodic/EnumerationEight")),
            ]));
    }
}
