using static StrataLint.Scribe.DefinitionDsl;

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
                new DocumentBlock.Describe(
                    DescribeId.Create("reversal-swaps-parity"),
                    DescribeKind.Theorem,
                    H("Reversal swaps parity in an even cycle"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.reversal_swaps_parity")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For an index inside a cycle of length twice a half-length, the reversed index has the opposite parity. This is an index calculation, not the narrative identity between a reversed canonical word and a rotation.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("matching-rotation-offset-is-odd"),
                    DescribeKind.Theorem,
                    H("A parity-matching rotation has odd offset"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.matching_rotation_offset_is_odd")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "If a rotated index is assumed to have the same parity as the reversed index, the rotation offset is odd. The premise connecting an actual periodic word to such a rotation remains explicit and unproved.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("even-offset-skeleton-count"),
                    DescribeKind.Theorem,
                    H("Half of the offsets in an even cycle are even"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.even_offset_skeleton_count")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Doubling gives an explicit equivalence from a half-length index type to the even offsets in the full cycle. The resulting count does not identify offsets with arithmetic orbit classes.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("full-exponent-stationing-count"),
                    DescribeKind.Theorem,
                    H("Full exponent choices multiply"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.full_exponent_stationing_count")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For labeled factors with independent exponent bounds, the number of bounded allocations is the product of the local capacities. No orbit-to-allocation map or bijection is supplied.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("mirror-normalization-is-unique"),
                    DescribeKind.Theorem,
                    H("Each Boolean mirror pair has a unique normalized member"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.mirror_normalization_is_unique")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Pointwise Boolean complement exchanges the two labeled sides. Choosing the member whose distinguished coordinate is false gives a unique representative among a stationing and its mirror.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("mirror-representative-count"),
                    DescribeKind.Theorem,
                    H("Mirror representatives have power-of-two cardinality"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.mirror_representative_count")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "After fixing the distinguished coordinate, all remaining Boolean coordinates are free, giving exactly two to the free-count representatives. This finite model implies no measured density or asymptotic exponent.")))))));
}
