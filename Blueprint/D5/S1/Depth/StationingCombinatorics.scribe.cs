using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth;

internal sealed class StationingCombinatoricsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Depth/StationingCombinatorics",
                "Record exact support and occupancy counts for labeled Boolean stationings."),
            H("Stationing Counts"),
            Blocks(
                Paragraph(Text(
                    "This module counts labeled Boolean stationings and their occupied supports. It does not assert that arithmetic orbits exhaust this Boolean model, and it does not close a finite certificate, measured exponent, density, or asymptotic law.")),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("stationing-count"),
                    H("All labeled stationings have power-of-two cardinality"),
                    LeanTheorem(
                        "D5/S1/Depth/StationingCombinatorics.stationing_count"),
                    LatexStatement.Create(@"$\forall n\in\mathbb{N},\ \operatorname{card}(\operatorname{Stationing}(n))=2^n$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Each labeled station independently chooses one of two Boolean sides, so the full configuration type has cardinality two to the station count. This ambient count does not provide an orbit encoding.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("occupied-stations-mirror"),
                    H("Mirroring complements the occupied support"),
                    LeanTheorem(
                        "D5/S1/Depth/StationingCombinatorics.occupied_stations_mirror"),
                    LatexStatement.Create(@"$\forall s\in\operatorname{Stationing}(n),\ \operatorname{Occ}(M(s))=\operatorname{Fin}(n)\setminus\operatorname{Occ}(s)$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Occupancy is the finite support of true Boolean coordinates. Pointwise negation sends that support to its complement inside the labeled station set; no sampled zero set is identified with this support.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("mirror-occupied-count"),
                    H("Mirror occupancy is the complementary count"),
                    LeanTheorem(
                        "D5/S1/Depth/StationingCombinatorics.mirror_occupied_count"),
                    LatexStatement.Create(@"$\forall s\in\operatorname{Stationing}(n),\ |\operatorname{Occ}(M(s))|=n-|\operatorname{Occ}(s)|$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Taking cardinalities in the support-complement identity gives the total station count minus the original occupancy. The finite identity supplies neither a density limit nor a repulsion exponent.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("mirror-stationing-ne-self"),
                    H("Boolean mirroring has no fixed nonempty stationing"),
                    LeanTheorem(
                        "D5/S1/Depth/StationingCombinatorics.mirror_stationing_ne_self"),
                    LatexStatement.Create(@"$\forall n>0,\ \forall s\in\operatorname{Stationing}(n),\ M(s)\neq s$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "On a nonempty labeled station set, the value at index zero differs from its Boolean negation, so no stationing is fixed. Applying this action to arithmetic orbits still requires the unresolved orbit-to-stationing bridge.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("occupied-count-stationing-count"),
                    H("A prescribed occupancy has binomial cardinality"),
                    LeanTheorem(
                        "D5/S1/Depth/StationingCombinatorics.occupied_count_stationing_count"),
                    LatexStatement.Create(@"$\forall n,k\in\mathbb{N},\ \operatorname{card}\{s\in\operatorname{Stationing}(n):|\operatorname{Occ}(s)|=k\}=\operatorname{choose}(n,k)$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The support equivalence identifies stationings with exactly k true coordinates and k-element subsets of the n labeled stations. Their exact count is the binomial coefficient; this does not prove either empirical zero-statistics law.")))
                ))));
}
