using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodic;

internal sealed class EnumerationTenDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var representatives = Id("goldenPeriodicOrbitRepresentativesExactlyTen");
        var valid = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("O"),
            representatives,
            Call("goldenCodedOrbitValid", Id("O")));
        var count = Equal(Call("length", representatives), Num(11));
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
            "Eleven exact primitive period-ten orbit certificates extend the golden data table.",
            H("Primitive Golden Period-Ten Certificates"),
            Blocks(
                Paragraph(Text(
                    "The period-ten branch words are solved exactly over Q(phi). Their closure, "
                        + "validity, separation from earlier periods, and low-arm witnesses are "
                        + "checked in bounded pairs and a final singleton.")),
                Describe.Lean(
                    DescribeId.Create("eleven-primitive-period-ten-orbits"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationTenData."
                            + "golden_new_periodic_orbit_count_ten"),
                    H("Eleven primitive period-ten orbits"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(count)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The exact table contains eleven representatives, each carrying a "
                            + "ten-step closed itinerary."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("period-ten-representatives-are-valid"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationTenData."
                            + "golden_new_periodic_orbit_representatives_valid_ten"),
                    H("The period-ten representatives are valid"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(valid)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every displayed code remains in the unit interval and follows the "
                            + "source, target, and affine rules of its branch word."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("one-hundred-ten-new-state-codes-are-distinct"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationTenData."
                            + "golden_new_periodic_orbit_state_codes_nodup_ten"),
                    H("The one hundred ten new state codes are distinct"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(nodup)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Flattening the eleven ten-cycles produces no repeated exact state "
                            + "code and no collision with the earlier enumeration."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("period-ten-low-arms-obey-the-golden-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationTenData."
                            + "golden_new_periodic_orbit_low_arms_bounded_ten"),
                    H("Period-ten low arms obey the golden bound"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(lowBound)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Each new cycle has an explicit member whose arm is at most the exact "
                            + "golden threshold."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenPeriodic/EnumerationNine")),
            ]));
    }
}
