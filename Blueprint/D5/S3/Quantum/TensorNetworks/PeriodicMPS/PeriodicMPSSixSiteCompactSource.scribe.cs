using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteCompactSourceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCompactSource";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The compact six-site trace graph and its observation",
        H("The compact six-site trace graph and its observation"),
        Blocks(
            Claim("source_isCompact", "Compact projective source",
                "The closure of the ordinary graph lies in the product of the invariant and amplitude projector spaces."),
            Claim("eq_graphPoint_of_amplitude_ne_zero", "Ordinary rays",
                "Off the base conics, the incidence equations identify the amplitude projector with the cubic image of the invariant tuple."),
            Claim("continuousOn_observation", "Continuous physical observation",
                "The adjacent marginal is a linear contraction of the amplitude projector divided by a strictly positive trace."),
            Claim("actual_state_lifts", "Literal observations of actual cores",
                "Every nonzero actual amplitude has a compact lift with the trace-normalized adjacent marginal."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpssixsitecompactsource-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
