using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal;

internal sealed class EscapeCountDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Lawvere =
        LibraryNoteRef.Create("D5/L/Diagonal/lawvere1969diagonal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Diagonal/EscapeCount",
            "Finite diagonal listings admit an exact count of those escaped by self-application."),
        H("Diagonal Escape Count"),
        Blocks(
            DocumentBlock.Describe.Lemma(
                DescribeId.Create("landing-on-the-diagonal-produces-a-fixed-point"),
                H("Landing on the diagonal produces a fixed point"),
                LeanTheorem(
                    "D5/S0/Diagonal/EscapeCount.diagonal_landing_fixed"),
                FormulaDsl.Disp(new Formula.Logic(
                    Equal(Call("g", Id("a0")), Call("diagonal", Id("f"), Id("g"))),
                    FormulaLogicOperator.Implies,
                    Equal(
                        Call("f", Call("g", Id("a0"), Id("a0"))),
                        Call("g", Id("a0"), Id("a0"))))),
                DescribeProvenance.LiteratureAttested(Lawvere),
                Blocks(Paragraph(Text(
                    "If a listed row equals its twisted diagonal, evaluating that equality at "
                    + "the row's own address shows that the diagonal entry is fixed by the "
                    + "twist. This is the set-level landing step in Lawvere's qualitative "
                    + "diagonal fixed-point argument.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("escaped-listings-have-an-exact-cardinality"),
                H("Escaped listings have an exact cardinality"),
                LeanTheorem(
                    "D5/S0/Diagonal/EscapeCount.escaped_listing_card"),
                FormulaDsl.Disp(Equal(
                    Call("card", Call("escapedListings", Id("f"))),
                    new Formula.Power(
                        Subtract(
                            new Formula.Power(Call("card", Id("Y")), Call("card", Id("A"))),
                            Call("card", Call("Fix", Id("f")))),
                        Call("card", Id("A"))))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For finite address and value types, the number of listings whose twisted "
                    + "diagonal is absent from the listing is the address-cardinality power of "
                    + "the number of value functions minus the fixed points of the twist. The "
                    + "proof separates each listing into its diagonal and independent "
                    + "off-diagonal row blocks.")))
            ))));
}
