using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SectorChannels;

internal sealed class SchmidtPartitionStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sorted spectral caps certify a quantitative distance to exact Schmidt partitions.",
        H("A quantitative inverse bound for labeled Schmidt partitions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sorted-partition-inverse"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/SectorChannels/SchmidtPartitionStability.sorted_partition_inverse"),
                H("Exact finite partition distance from sorted spectral data"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The readout is the minimum absolute label-weight error over all finite assignments of the squared Schmidt amplitudes. It uses arbitrary normalized label weights, any finite positive label count, and allows padded zero amplitudes.")),
                    Paragraph(Text("From sorted nonnegative spectral amplitudes, prefix majorization and the cap-overlap inequality, Abel summation bounds the cross correlation. Cauchy-Schwarz on the squared difference then controls the actual grouped Schmidt error. Eliminating the unobserved spectral mass deficit produces the small-error inverse curve, the large-error linear bound, and the spacing gap 2/[T(T+1)].")),
                    Paragraph(Text("This theorem consumes scalar spectral premises. It does not formalize the channel-to-Gram implication, the Schur-Horn frame converse, Fourier optimality, computational complexity, or the original coherent RT problem."))),
                DescribeRole.Theorem))));
}
