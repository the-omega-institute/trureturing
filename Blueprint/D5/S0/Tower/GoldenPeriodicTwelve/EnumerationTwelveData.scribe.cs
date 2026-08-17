using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodicTwelve;

internal sealed class EnumerationTwelveDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var representatives = Id("goldenPeriodicOrbitRepresentativesExactlyTwelve");
        var count = Equal(Call("length", representatives), Num(25));
        var valid = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("O"),
            representatives,
            Call("goldenCodedOrbitValid", Id("O")));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Twenty-five exact primitive period-twelve orbit certificates extend the golden table.",
            H("Primitive Golden Period-Twelve Certificates"),
            Blocks(
                Paragraph(Text(
                    "The period-twelve branch words and quadratic coordinates are stated "
                        + "exactly over Q(phi).")),
                Describe.Lean(
                    DescribeId.Create("twenty-five-primitive-period-twelve-orbits"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveData."
                            + "golden_new_periodic_orbit_count_twelve"),
                    H("Twenty-five primitive period-twelve orbits"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(count)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Each representative carries a twelve-step closed itinerary."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("period-twelve-representatives-are-valid"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveData."
                            + "golden_new_periodic_orbit_representatives_valid_twelve"),
                    H("The period-twelve representatives are valid"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(valid)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every displayed code follows its source, target, and affine branch "
                            + "rules and closes after twelve steps."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenPeriodic/EnumerationEleven")),
            ]));
    }
}
