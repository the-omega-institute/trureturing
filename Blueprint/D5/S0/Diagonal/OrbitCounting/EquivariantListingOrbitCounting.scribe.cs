using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.OrbitCounting;

internal sealed class EquivariantListingOrbitCountingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef VanLintWilson =
        LibraryNoteRef.Create("D5/L/Diagonal/vanlintwilson2001course");

    public DocumentDefinition Create()
    {
        var group = Id("G");
        var addresses = Id("A");
        var values = Id("Y");
        var listings = Call("card", Call("EquivariantListing", group, addresses, values));
        var valueCard = Call("card", values);
        var diagonalOrbits = Call("card", Call("OrbitIndex", group, Call("prod", addresses, addresses)));
        var fixedPairAverage = Call("natDiv",
            Call("sumFixedDiagonalPairs", group, addresses), Call("card", group));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Equivariant listings are functions on diagonal-action orbits, whose number is given by Burnside averaging.",
            H("Orbit Counting for Equivariant Listings"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("equivariant-listings-are-counted-by-diagonal-action-orbits"),
                    DeclarationHandle.Create(
                        "D5/S0/Diagonal/OrbitCounting/EquivariantListingOrbitCounting."
                            + "equivariant_listing_card_orbits"),
                    H("Equivariant listings are counted by diagonal-action orbits"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(Equal(
                        listings,
                        new Formula.Power(valueCard, diagonalOrbits)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Simultaneous transport acts diagonally on ordered address pairs. "
                            + "Equivariance says exactly that a listing is constant on each orbit, "
                            + "so choosing an arbitrary Y-value for every orbit gives all and only "
                            + "the equivariant listings."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("burnside-average-is-the-equivariant-listing-exponent"),
                    DeclarationHandle.Create(
                        "D5/S0/Diagonal/OrbitCounting/EquivariantListingOrbitCounting."
                            + "equivariant_listing_card_burnside"),
                    H("Burnside average is the equivariant-listing exponent"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(Equal(
                        listings,
                        new Formula.Power(valueCard, fixedPairAverage)))),
                    AssessedProvenance.FromLiterature(VanLintWilson),
                    Blocks(Paragraph(Text(
                        "Burnside's lemma identifies the number of diagonal-action orbits with "
                            + "the sum, over group elements, of the number of fixed ordered address "
                            + "pairs divided in Nat by the group cardinality. Mathlib's exact "
                            + "Burnside theorem proves the divisibility and the average identity; "
                            + "the repository orbit equivalence turns that orbit count into the "
                            + "exponent of card(Y)."))),
                    DescribeRole.Theorem),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Diagonal/EquivariantEscape")),
            ]));
    }
}
