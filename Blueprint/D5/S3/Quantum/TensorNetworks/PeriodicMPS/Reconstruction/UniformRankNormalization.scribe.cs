using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class UniformRankNormalizationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/UniformRankNormalization";
    private const string Title = "Normalization and rank of the two-site marginal";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("uniformranknormalization"),
                DeclarationHandle.Create(Module + ".finrank_rawReadout_span"),
                H("Rank of the trace-one observation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a nonzero trace-word amplitude, the span of the raw derivative and raw radial vector has dimension one more than the normalized marginal derivative. Passing to readout coordinates preserves the normalized rank."))),
                DescribeRole.Theorem))));
}
