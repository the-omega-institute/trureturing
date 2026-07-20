using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class StationingCountsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Phase/StationingCounts",
                "Record exact support and occupancy counts for labeled Boolean stationings."),
            H("Stationing Counts"),
            Blocks(
                Paragraph(Text(
                    "This module counts labeled Boolean stationings and their occupied supports. It does not assert that arithmetic orbits exhaust this Boolean model, and it does not close a finite certificate, measured exponent, density, or asymptotic law.")),
                new DocumentBlock.Describe(
                    DescribeId.Create("stationing-count"),
                    DescribeKind.Theorem,
                    H("All labeled stationings have power-of-two cardinality"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/StationingCounts.stationing_count")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Each labeled station independently chooses one of two Boolean sides, so the full configuration type has cardinality two to the station count. This ambient count does not provide an orbit encoding."))),
                    LatexStatement.Create(@"$\forall n\in\mathbb{N},\ \operatorname{card}(\operatorname{Stationing}(n))=2^n$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("occupied-stations-mirror"),
                    DescribeKind.Theorem,
                    H("Mirroring complements the occupied support"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/StationingCounts.occupied_stations_mirror")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Occupancy is the finite support of true Boolean coordinates. Pointwise negation sends that support to its complement inside the labeled station set; no sampled zero set is identified with this support."))),
                    LatexStatement.Create(@"$\forall s\in\operatorname{Stationing}(n),\ \operatorname{Occ}(M(s))=\operatorname{Fin}(n)\setminus\operatorname{Occ}(s)$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("mirror-occupied-count"),
                    DescribeKind.Theorem,
                    H("Mirror occupancy is the complementary count"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/StationingCounts.mirror_occupied_count")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Taking cardinalities in the support-complement identity gives the total station count minus the original occupancy. The finite identity supplies neither a density limit nor a repulsion exponent."))),
                    LatexStatement.Create(@"$\forall s\in\operatorname{Stationing}(n),\ |\operatorname{Occ}(M(s))|=n-|\operatorname{Occ}(s)|$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("mirror-stationing-ne-self"),
                    DescribeKind.Theorem,
                    H("Boolean mirroring has no fixed nonempty stationing"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/StationingCounts.mirror_stationing_ne_self")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "On a nonempty labeled station set, the value at index zero differs from its Boolean negation, so no stationing is fixed. Applying this action to arithmetic orbits still requires the unresolved orbit-to-stationing bridge."))),
                    LatexStatement.Create(@"$\forall n>0,\ \forall s\in\operatorname{Stationing}(n),\ M(s)\neq s$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("occupied-count-stationing-count"),
                    DescribeKind.Theorem,
                    H("A prescribed occupancy has binomial cardinality"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/StationingCounts.occupied_count_stationing_count")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The support equivalence identifies stationings with exactly k true coordinates and k-element subsets of the n labeled stations. Their exact count is the binomial coefficient; this does not prove either empirical zero-statistics law."))),
                    LatexStatement.Create(@"$\forall n,k\in\mathbb{N},\ \operatorname{card}\{s\in\operatorname{Stationing}(n):|\operatorname{Occ}(s)|=k\}=\operatorname{choose}(n,k)$")))));
}
