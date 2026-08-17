using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodic;

internal sealed class EnumerationElevenDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var representatives = Id("goldenPeriodicOrbitRepresentativesExactlyEleven");
        var count = Equal(Call("length", representatives), Num(18));
        var valid = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("O"),
            representatives,
            Call("goldenCodedOrbitValid", Id("O")));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Eighteen exact primitive period-eleven orbit certificates extend the golden table.",
            H("Primitive Golden Period-Eleven Certificates"),
            Blocks(
                Paragraph(Text(
                    "The period-eleven branch words and quadratic coordinates are stated "
                        + "exactly over Q(phi).")),
                Describe.Lean(
                    DescribeId.Create("eighteen-primitive-period-eleven-orbits"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationElevenData."
                            + "golden_new_periodic_orbit_count_eleven"),
                    H("Eighteen primitive period-eleven orbits"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(count)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Each representative carries an eleven-step closed itinerary."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("period-eleven-representatives-are-valid"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationElevenData."
                            + "golden_new_periodic_orbit_representatives_valid_eleven"),
                    H("The period-eleven representatives are valid"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(valid)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every displayed code follows its source, target, and affine branch "
                            + "rules and closes after eleven steps."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenPeriodic/EnumerationTen")),
            ]));
    }
}
