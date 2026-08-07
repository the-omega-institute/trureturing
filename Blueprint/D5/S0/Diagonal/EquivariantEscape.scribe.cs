using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal;

internal sealed class EquivariantEscapeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var cardY = Call("card", Id("Y"));
        var fixedPoints = Call("card", Call("Fix", Id("f")));
        var omega = new Formula.Subscript(Id("omega"), Id("i"));
        var orbitFactor = Subtract(new Formula.Power(cardY, omega), fixedPoints);
        var escaped = Call("card", Call("escapedEquivariantListings", Id("f")));

        return DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S0/Diagonal/EquivariantEscape",
                "Equivariant diagonal escape counts factor exactly over the action orbits."),
            H("Equivariant Diagonal Escape"),
            Blocks(
                DocumentBlock.Describe.Lemma(
                    DescribeId.Create("equivariant-diagonals-are-orbit-constant"),
                    H("Equivariant diagonals are orbit-constant"),
                    LeanTheorem(
                        "D5/S0/Diagonal/EquivariantEscape.equivariant_diagonal_constant"),
                    FormulaDsl.Disp(Equal(
                        Call("g", Call("smul", Id("sigma"), Id("a")),
                            Call("smul", Id("sigma"), Id("a"))),
                        Call("g", Id("a"), Id("a")))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Simultaneous equivariance in the row and column coordinates makes "
                        + "the diagonal value unchanged under transport by any group element. "
                        + "Thus each address orbit contributes one diagonal coordinate.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("equivariant-escape-counts-factor-by-address-orbit"),
                    H("Equivariant escape counts factor by address orbit"),
                    LeanTheorem(
                        "D5/S0/Diagonal/EquivariantEscape.equivariant_escaped_card"),
                    FormulaDsl.Disp(Equal(
                        escaped,
                        Call("productOrbits", orbitFactor, Id("i")))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Choose explicit stabilizer-orbit coordinates for the equivariant "
                        + "listings. After revealing the orbit-diagonal values, each address "
                        + "orbit has one forbidden off-diagonal row exactly when its diagonal "
                        + "value is fixed by the twist. Finite sums of these independent row "
                        + "choices separate into the product of card(Y)^omega_i minus the "
                        + "fixed-point count.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("transitive-actions-have-one-escape-factor"),
                    H("Transitive actions have one escape factor"),
                    LeanTheorem(
                        "D5/S0/Diagonal/EquivariantEscape.transitive_equivariant_escaped_card"),
                    FormulaDsl.Disp(Equal(escaped, orbitFactor)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For a transitive action the address-orbit quotient has one element, "
                        + "so the general product reduces to the single factor determined by "
                        + "the stabilizer-orbit count.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("trivial-orbit-data-recovers-the-free-count"),
                    H("Trivial orbit data recovers the free count"),
                    LeanTheorem(
                        "D5/S0/Diagonal/EquivariantEscape.trivial_action_recovers_escaped_listing_card"),
                    FormulaDsl.Disp(Equal(
                        Call("productAddresses", Subtract(
                            new Formula.Power(cardY, Call("card", Id("A"))),
                            fixedPoints)),
                        Call("card", Call("escapedListings", Id("f"))))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "When every address is its own orbit and each stabilizer-orbit block "
                        + "has the full address cardinality, the product side is the frozen "
                        + "unrestricted escaped-listing count.")))
                ))));
    }
}
