using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSUniformHardCoreWitnessAmplitudeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreWitnessAmplitude";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The independent-set indicator as a rank-one-core trace tensor",
        H("Rank-one products around a cycle"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodic-rank-one-trace-product"),
                DeclarationHandle.Create(Module + ".traceWord_rankOne"),
                H("Cyclic product of adjacent dot products"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a nonempty word and outer-product cores uₐvₐᵀ, the trace amplitude is the product of vₐᵀuᵦ over ordered adjacent symbols around the cycle. Multiplying the rank-one factors produces the dot products along the word, and the trace supplies the last-to-first dot product."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodic-hard-core-trace-indicator"),
                DeclarationHandle.Create(Module + ".traceWord_witnessCore_eq_indicator"),
                H("Literal independent-set amplitudes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the two explicit witness cores the adjacent dot product is zero on 11 and one on 00, 01 and 10. Thus at each length n ≥ 7 the trace amplitude is exactly one on words whose occupied sites are independent in the cycle, and zero on every other word. The trace enforces the exclusion across the seam."))),
                DescribeRole.Theorem))));
}
