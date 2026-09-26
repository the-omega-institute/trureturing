using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalReadoutAtomicSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Mechanical/MechanicalReadoutAtomicSeries.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The completed mechanical readout has an absolutely summable floor expansion with unit atomic mass.",
        H("Mechanical Readout Atomic Series"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mechanical-readout-atomic-series-mass"),
                DeclarationHandle.Create(Prefix + "geometric_readout_floor_series_and_mass"),
                H("Floor series and mass normalization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix a geometric ratio in [0,1), a slope in [0,1], and a phase in [0,1). The completed readout is the sum, over positive times k, of the actual cumulative floor at time k weighted by (1-r)^2 r^(k-1). The sum of these weights multiplied by k is exactly one. Absolute summability follows from the bound of the cumulative floor by k. The proof expands each actual mechanical letter as the difference of two successive floors, shifts the convergent series, and evaluates the linearly weighted geometric series. At time k the floor equals the number of thresholds (i-x)/k, for i from one through k, that the slope has crossed. Substitution gives an exact atomic distribution-function series. Constructing its probability measure and identifying the exact jumps require further arguments."))),
                DescribeRole.Theorem))));
}
