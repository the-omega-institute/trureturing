using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

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
                    In(Seq(Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, Operatorname, Grp(F.Id("card")), Open, Operatorname, Grp(F.Id("Stationing")), Open, F.Id("n"), Close, Close, Eq, D(2), Caret, F.Id("n"))),                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Each labeled station independently chooses one of two Boolean sides, so the full configuration type has cardinality two to the station count. This ambient count does not provide an orbit encoding.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("occupied-stations-mirror"),
                    H("Mirroring complements the occupied support"),
                    LeanTheorem(
                        "D5/S1/Depth/StationingCombinatorics.occupied_stations_mirror"),
                    In(Seq(Forall, Sp, F.Id("s"), InMacro, Operatorname, Grp(F.Id("Stationing")), Open, F.Id("n"), Close, Comma, Esc, Operatorname, Grp(F.Id("Occ")), Open, F.Id("M"), Open, F.Id("s"), Close, Close, Eq, Operatorname, Grp(F.Id("Fin")), Open, F.Id("n"), Close, Setminus, Operatorname, Grp(F.Id("Occ")), Open, F.Id("s"), Close)),                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Occupancy is the finite support of true Boolean coordinates. Pointwise negation sends that support to its complement inside the labeled station set; no sampled zero set is identified with this support.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("mirror-occupied-count"),
                    H("Mirror occupancy is the complementary count"),
                    LeanTheorem(
                        "D5/S1/Depth/StationingCombinatorics.mirror_occupied_count"),
                    In(Seq(Forall, Sp, F.Id("s"), InMacro, Operatorname, Grp(F.Id("Stationing")), Open, F.Id("n"), Close, Comma, Esc, Bar, Operatorname, Grp(F.Id("Occ")), Open, F.Id("M"), Open, F.Id("s"), Close, Close, Bar, Eq, F.Id("n"), Minus, Bar, Operatorname, Grp(F.Id("Occ")), Open, F.Id("s"), Close, Bar)),                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Taking cardinalities in the support-complement identity gives the total station count minus the original occupancy. The finite identity supplies neither a density limit nor a repulsion exponent.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("mirror-stationing-ne-self"),
                    H("Boolean mirroring has no fixed nonempty stationing"),
                    LeanTheorem(
                        "D5/S1/Depth/StationingCombinatorics.mirror_stationing_ne_self"),
                    In(Seq(Forall, Sp, F.Id("n"), Gt, D(0), Comma, Esc, Forall, Sp, F.Id("s"), InMacro, Operatorname, Grp(F.Id("Stationing")), Open, F.Id("n"), Close, Comma, Esc, F.Id("M"), Open, F.Id("s"), Close, Neq, Sp, F.Id("s"))),                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "On a nonempty labeled station set, the value at index zero differs from its Boolean negation, so no stationing is fixed. Applying this action to arithmetic orbits still requires the unresolved orbit-to-stationing bridge.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("occupied-count-stationing-count"),
                    H("A prescribed occupancy has binomial cardinality"),
                    LeanTheorem(
                        "D5/S1/Depth/StationingCombinatorics.occupied_count_stationing_count"),
                    In(Seq(Forall, Sp, F.Id("n"), Comma, F.Id("k"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, Operatorname, Grp(F.Id("card")), OpenBrace, F.Id("s"), InMacro, Operatorname, Grp(F.Id("Stationing")), Open, F.Id("n"), Close, Colon, Bar, Operatorname, Grp(F.Id("Occ")), Open, F.Id("s"), Close, Bar, Eq, F.Id("k"), CloseBrace, Eq, Operatorname, Grp(F.Id("choose")), Open, F.Id("n"), Comma, F.Id("k"), Close)),                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The support equivalence identifies stationings with exactly k true coordinates and k-element subsets of the n labeled stations. Their exact count is the binomial coefficient; this does not prove either empirical zero-statistics law.")))
                ))));
}
