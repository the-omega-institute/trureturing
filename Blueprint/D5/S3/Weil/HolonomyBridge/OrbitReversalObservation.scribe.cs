using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.HolonomyBridge;

internal sealed class OrbitReversalObservationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/HolonomyBridge/OrbitReversalObservation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The existing Weil orbit parity channels realize the hidden-idempotent classification of visible negation.",
        H("Orbit Reversal Observation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("orbit-reversal-observation-pairswap"),
                DeclarationHandle.Create(Prefix + "pairSwap"),
                H("pairSwap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exchange the actual pair of spectral readouts."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("orbit-reversal-observation-oddobservation"),
                DeclarationHandle.Create(Prefix + "oddObservation"),
                H("oddObservation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The frozen odd spectral channel, with its existing normalization."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("orbit-reversal-observation-fixedpart-eq-even-channel"),
                DeclarationHandle.Create(Prefix + "fixedPart_eq_even_channel"),
                H("fixedPart eq even channel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The hidden fixed part is exactly the existing even spectral channel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("orbit-reversal-observation-weil-visible-negation-lift"),
                DeclarationHandle.Create(Prefix + "weil_visible_negation_lift"),
                H("weil visible negation lift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same general lift theorem applies to the actual odd Weil readout. Its entire fixed component is invisible to that readout."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("orbit-reversal-observation-off-line-orbit-in-reversal-coordinates"),
                DeclarationHandle.Create(Prefix + "off_line_orbit_in_reversal_coordinates"),
                H("off line orbit in reversal coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The source's actual off-line orbit has the same energy decomposition in the reversal-observation coordinates. This consumes the original theorem."))),
                DescribeRole.Theorem))));
}
