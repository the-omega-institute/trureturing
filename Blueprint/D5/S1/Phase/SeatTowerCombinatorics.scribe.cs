using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class SeatTowerCombinatoricsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Phase/SeatTowerCombinatorics",
                "Record exact parity and finite-cardinality skeletons for mirror stationing."),
            H("Seat-Tower Combinatorics"),
            Blocks(
                Paragraph(Text(
                    "This module works with labeled finite indices, independent bounded exponent choices, and Boolean stationings. It does not identify arithmetic orbits with stationings, derive a selector from Jacobi data, or supply any finite orbit certificate. No finite observation, measured exponent, density, or asymptotic law is closed by these theorems.")),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("reversal-swaps-parity"),
                    H("Reversal swaps parity in an even cycle"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.reversal_swaps_parity"),
                    In(Seq(Forall, Sp, F.Id("h"), Comma, F.Id("i"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, F.Id("i"), Lt, D(2), F.Id("h"), Sp, Rightarrow, Sp, Open, D(2), F.Id("h"), Minus, D(1), Minus, F.Id("i"), Close, Operatorname, Grp(F.Id("mod")), D(2), Eq, D(1), Minus, Open, F.Id("i"), Operatorname, Grp(F.Id("mod")), D(2), Close)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For an index inside a cycle of length twice a half-length, the reversed index has the opposite parity. This is an index calculation, not the narrative identity between a reversed canonical word and a rotation.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("matching-rotation-offset-is-odd"),
                    H("A parity-matching rotation has odd offset"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.matching_rotation_offset_is_odd"),
                    Disp(Seq(Forall, Sp, F.Id("h"), Comma, F.Id("i"), Comma, F.Id("k"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, F.Id("i"), Lt, D(2), F.Id("h"), Sp, Land, Sp, Open, D(2), F.Id("h"), Minus, D(1), Minus, F.Id("i"), Close, Operatorname, Grp(F.Id("mod")), D(2), Eq, Open, F.Id("i"), Plus, F.Id("k"), Close, Operatorname, Grp(F.Id("mod")), D(2), Sp, Rightarrow, Sp, F.Id("k"), Operatorname, Grp(F.Id("mod")), D(2), Eq, D(1))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "If a rotated index is assumed to have the same parity as the reversed index, the rotation offset is odd. The premise connecting an actual periodic word to such a rotation remains explicit and unproved.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("even-offset-skeleton-count"),
                    H("Half of the offsets in an even cycle are even"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.even_offset_skeleton_count"),
                    In(Seq(Forall, Sp, F.Id("h"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, Operatorname, Grp(F.Id("card")), Open, Operatorname, Grp(F.Id("EvenOffset")), Open, F.Id("h"), Close, Close, Eq, F.Id("h"))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Doubling gives an explicit equivalence from a half-length index type to the even offsets in the full cycle. The resulting count does not identify offsets with arithmetic orbit classes.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("full-exponent-stationing-count"),
                    H("Full exponent choices multiply"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.full_exponent_stationing_count"),
                    Disp(Seq(Forall, Sp, F.Id("p"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, Forall, Sp, F.Id("e"), Colon, Operatorname, Grp(F.Id("Fin")), Open, F.Id("p"), Close, To, Mathbb, Grp(F.Id("N")), Comma, Esc, Operatorname, Grp(F.Id("card")), NegThin, Left, Open, Prod, Underscore, Grp(F.Id("i"), InMacro, Operatorname, Grp(F.Id("Fin")), Open, F.Id("p"), Close), Operatorname, Grp(F.Id("Fin")), Open, F.Id("e"), Open, F.Id("i"), Close, Plus, D(1), Close, Right, Close, Eq, Prod, Underscore, Grp(F.Id("i"), InMacro, Operatorname, Grp(F.Id("Fin")), Open, F.Id("p"), Close), Open, F.Id("e"), Open, F.Id("i"), Close, Plus, D(1), Close)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For labeled factors with independent exponent bounds, the number of bounded allocations is the product of the local capacities. No orbit-to-allocation map or bijection is supplied.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("mirror-normalization-is-unique"),
                    H("Each Boolean mirror pair has a unique normalized member"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.mirror_normalization_is_unique"),
                    Disp(Seq(Forall, Sp, F.Id("f"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, Forall, Sp, F.Id("s"), InMacro, Operatorname, Grp(F.Id("Stationing")), Open, F.Id("f"), Plus, D(1), Close, Comma, Esc, Operatorname, Grp(F.Id("Rep")), Open, F.Id("N"), Open, F.Id("s"), Close, Close, Sp, Land, Sp, Open, F.Id("N"), Open, F.Id("s"), Close, Eq, F.Id("s"), Sp, Lor, Sp, F.Id("N"), Open, F.Id("s"), Close, Eq, F.Id("M"), Open, F.Id("s"), Close, Close, Sp, Land, Sp, Forall, Sp, F.Id("r"), Comma, Esc, Operatorname, Grp(F.Id("Rep")), Open, F.Id("r"), Close, Sp, Land, Sp, Open, F.Id("r"), Eq, F.Id("s"), Sp, Lor, Sp, F.Id("r"), Eq, F.Id("M"), Open, F.Id("s"), Close, Close, Sp, Rightarrow, Sp, F.Id("r"), Eq, F.Id("N"), Open, F.Id("s"), Close)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Pointwise Boolean complement exchanges the two labeled sides. Choosing the member whose distinguished coordinate is false gives a unique representative among a stationing and its mirror.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("mirror-representative-count"),
                    H("Mirror representatives have power-of-two cardinality"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.mirror_representative_count"),
                    Disp(Seq(Forall, Sp, F.Id("f"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, Operatorname, Grp(F.Id("card")), OpenBrace, F.Id("s"), InMacro, Operatorname, Grp(F.Id("Stationing")), Open, F.Id("f"), Plus, D(1), Close, Mid, Operatorname, Grp(F.Id("Rep")), Open, F.Id("s"), Close, CloseBrace, Eq, D(2), Caret, Grp(F.Id("f")))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "After fixing the distinguished coordinate, all remaining Boolean coordinates are free, giving exactly two to the free-count representatives. This finite model implies no measured density or asymptotic exponent.")))
                ))));
}
