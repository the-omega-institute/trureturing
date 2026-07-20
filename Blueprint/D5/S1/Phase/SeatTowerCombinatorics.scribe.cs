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
                        "For an index inside a cycle of length twice a half-length, the reversed index has the opposite parity. This is an index calculation, not the narrative identity between a reversed canonical word and a rotation."))),
                    LatexStatement.Create(@"$\forall h,i\in\mathbb{N},\ i<2h \Rightarrow (2h-1-i)\operatorname{mod}2=1-(i\operatorname{mod}2)$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("matching-rotation-offset-is-odd"),
                    DescribeKind.Theorem,
                    H("A parity-matching rotation has odd offset"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.matching_rotation_offset_is_odd")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "If a rotated index is assumed to have the same parity as the reversed index, the rotation offset is odd. The premise connecting an actual periodic word to such a rotation remains explicit and unproved."))),
                    LatexStatement.Create(@"$$\forall h,i,k\in\mathbb{N},\ i<2h \land (2h-1-i)\operatorname{mod}2=(i+k)\operatorname{mod}2 \Rightarrow k\operatorname{mod}2=1$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("even-offset-skeleton-count"),
                    DescribeKind.Theorem,
                    H("Half of the offsets in an even cycle are even"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.even_offset_skeleton_count")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Doubling gives an explicit equivalence from a half-length index type to the even offsets in the full cycle. The resulting count does not identify offsets with arithmetic orbit classes."))),
                    LatexStatement.Create(@"$\forall h\in\mathbb{N},\ \operatorname{card}(\operatorname{EvenOffset}(h))=h$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("full-exponent-stationing-count"),
                    DescribeKind.Theorem,
                    H("Full exponent choices multiply"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.full_exponent_stationing_count")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For labeled factors with independent exponent bounds, the number of bounded allocations is the product of the local capacities. No orbit-to-allocation map or bijection is supplied."))),
                    LatexStatement.Create(@"$$\forall p\in\mathbb{N},\ \forall e:\operatorname{Fin}(p)\to\mathbb{N},\ \operatorname{card}\!\left(\prod_{i\in\operatorname{Fin}(p)}\operatorname{Fin}(e(i)+1)\right)=\prod_{i\in\operatorname{Fin}(p)}(e(i)+1)$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("stationing-count"),
                    DescribeKind.Theorem,
                    H("All labeled stationings have power-of-two cardinality"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.stationing_count")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Each labeled station independently chooses one of two Boolean sides, so the full configuration type has cardinality two to the station count. This ambient count does not assert that arithmetic orbits exhaust the Boolean model."))),
                    LatexStatement.Create(@"$\forall n\in\mathbb{N},\ \operatorname{card}(\operatorname{Stationing}(n))=2^n$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("occupied-stations-mirror"),
                    DescribeKind.Theorem,
                    H("Mirroring complements the occupied support"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.occupied_stations_mirror")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Occupancy is defined as the finite support of true Boolean coordinates. Pointwise negation therefore sends that support to its complement inside the labeled station set; no sampled zero set is identified with this support."))),
                    LatexStatement.Create(@"$\forall s\in\operatorname{Stationing}(n),\ \operatorname{Occ}(M(s))=\operatorname{Fin}(n)\setminus\operatorname{Occ}(s)$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("mirror-occupied-count"),
                    DescribeKind.Theorem,
                    H("Mirror occupancy is the complementary count"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.mirror_occupied_count")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Taking cardinalities in the support-complement identity gives the total station count minus the original occupancy. The finite identity supplies neither a density limit nor a repulsion exponent."))),
                    LatexStatement.Create(@"$\forall s\in\operatorname{Stationing}(n),\ |\operatorname{Occ}(M(s))|=n-|\operatorname{Occ}(s)|$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("mirror-stationing-ne-self"),
                    DescribeKind.Theorem,
                    H("Boolean mirroring has no fixed nonempty stationing"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.mirror_stationing_ne_self")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "On a nonempty labeled station set, the value at index zero differs from its Boolean negation, so no stationing is fixed. Applying this fixed-point-free action to arithmetic orbits still requires the unresolved orbit-to-stationing bridge."))),
                    LatexStatement.Create(@"$\forall n>0,\ \forall s\in\operatorname{Stationing}(n),\ M(s)\neq s$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("occupied-count-stationing-count"),
                    DescribeKind.Theorem,
                    H("A prescribed occupancy has binomial cardinality"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.occupied_count_stationing_count")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The support equivalence identifies stationings with exactly k true coordinates and k-element subsets of the n labeled stations. Their exact count is the binomial coefficient; this does not prove either empirical zero-statistics law."))),
                    LatexStatement.Create(@"$\forall n,k\in\mathbb{N},\ \operatorname{card}\{s\in\operatorname{Stationing}(n):|\operatorname{Occ}(s)|=k\}=\operatorname{choose}(n,k)$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("mirror-normalization-is-unique"),
                    DescribeKind.Theorem,
                    H("Each Boolean mirror pair has a unique normalized member"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.mirror_normalization_is_unique")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Pointwise Boolean complement exchanges the two labeled sides. Choosing the member whose distinguished coordinate is false gives a unique representative among a stationing and its mirror."))),
                    LatexStatement.Create(@"$$\forall f\in\mathbb{N},\ \forall s\in\operatorname{Stationing}(f+1),\ \operatorname{Rep}(N(s)) \land (N(s)=s \lor N(s)=M(s)) \land \forall r,\ \operatorname{Rep}(r) \land (r=s \lor r=M(s)) \Rightarrow r=N(s)$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("mirror-representative-count"),
                    DescribeKind.Theorem,
                    H("Mirror representatives have power-of-two cardinality"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerCombinatorics.mirror_representative_count")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "After fixing the distinguished coordinate, all remaining Boolean coordinates are free, giving exactly two to the free-count representatives. This finite model implies no measured density or asymptotic exponent."))),
                    LatexStatement.Create(@"$$\forall f\in\mathbb{N},\ \operatorname{card}\{s\in\operatorname{Stationing}(f+1)\mid\operatorname{Rep}(s)\}=2^{f}$$")))));
}
