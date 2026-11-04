using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.PeriodicOrbits;

internal sealed class SkewZModFixedCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed points of a finite cyclic skew product are exactly zero-holonomy base returns, with one factor for every fiber phase.",
        H("Fixed points and zero holonomy in a cyclic skew product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("skew-zmod-fixed-count"),
                DeclarationHandle.Create("D5/S1/Dynamics/PeriodicOrbits/SkewZModFixedCount.fixed_count_skew_zmod"),
                H("Fixed-point counting through the holonomy kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an additive skew map with fiber ZMod q, an n-step fixed point "
                        + "must first have an n-step fixed base point. Its fiber coordinate then "
                        + "returns exactly when the n-step Birkhoff sum is zero in ZMod q.")),
                    Paragraph(Text(
                        "When the holonomy vanishes, every one of the q fiber phases returns; "
                        + "when it does not, no phase returns. The fixed-point count is therefore "
                        + "q times the cardinality of the zero-holonomy return set. This is the "
                        + "counting bridge from the skew group action to the Möbius/Dold layer."))),
                DescribeRole.Theorem)
        )));
}
