using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class UnitaryTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Invariant optimized distance under unitary boundaries",
        H("Invariant optimized distance under unitary boundaries"),
        Blocks(Describe.Lean(
            DescribeId.Create("transport-distance-set"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnitaryTransport.transport_distance_set"),
            H("Invariant optimized distance under unitary boundaries"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Initial register conjugation and terminal flag-conditioned conjugation act on the protocol class with an inverse. Their reference extensions preserve the trace norm, giving the same set of achievable diamond bounds."))),
            DescribeRole.Theorem))));
}
