using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.PeriodicOrbits;

internal sealed class SkewZModOrbitCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic fiber multiplicity survives Möbius inversion: exact lifted cycle counts factor through the zero-holonomy return table on the base.",
        H("Möbius orbit counts for cyclic additive skew products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("skew-zmod-orbit-count"),
                DeclarationHandle.Create("D5/S1/Dynamics/PeriodicOrbits/SkewZModOrbitCount.delta_fixed_count_skew_zmod"),
                H("Holonomy factorization of the Möbius transform"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a skew product with fiber ZMod q, every zero-holonomy base return "
                        + "lifts to all q phases. The fixed-point table is therefore q times "
                        + "the base zero-holonomy table. The Möbius transform is linear, so "
                        + "the same factor survives when fixed points are converted into exact "
                        + "cycle counts.")),
                    Paragraph(Text(
                        "The resulting identity says that the n-weighted primitive-cycle count "
                        + "is q times an explicitly computable base transform. This is an "
                        + "arithmetic shadow of the cyclic group action and yields a divisibility "
                        + "invariant even when individual cycle lengths vary with holonomy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("skew-zmod-weighted-cycle-count"),
                DeclarationHandle.Create("D5/S1/Dynamics/PeriodicOrbits/SkewZModOrbitCount.weighted_cycle_count_factorization"),
                H("Weighted exact-cycle factorization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The generic Möbius orbit-count identity identifies the transformed fixed-point "
                    + "table with n times the exact cycle multiplicity, so the holonomy factorization "
                    + "becomes an exact primitive-cycle formula."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("skew-zmod-dvd-weighted-cycle-count"),
                DeclarationHandle.Create("D5/S1/Dynamics/PeriodicOrbits/SkewZModOrbitCount.zmod_dvd_weighted_cycle_count"),
                H("Divisibility invariant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every positive-time weighted cycle count of a ZMod-q skew product is divisible "
                    + "by q, exposing the fiber cardinality as an invariant of the lifted action."))),
                DescribeRole.Theorem)
        )));
}
