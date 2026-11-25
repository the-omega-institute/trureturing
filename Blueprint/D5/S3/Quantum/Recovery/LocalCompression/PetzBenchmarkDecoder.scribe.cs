using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.LocalCompression;

internal sealed class PetzBenchmarkDecoderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary Petz recovery with reference reset composes on all matrices and transfers the exact retained-marginal benchmark under environmental compression.",
        H("Completed Petz recovery under environment compression"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completed-petz-transitivity"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/LocalCompression/PetzBenchmarkDecoder.completed_petz_transitivity"),
                H("Transitivity of the completed decoder"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Two normalized finite Kraus families define the two forward channels. The composite family consists of the products of their Kraus matrices. Each ordinary decoder uses the spectral inverse square root of the forward reference and resets the missing output weight to the input reference.")),
                    Paragraph(Text("Between reverse Kraus factors the inverse square root and square root multiply to the intermediate support projection. The projection fixes each reference-weighted forward Kraus image. The supported inner term has range in the intermediate support, and the outer decoder maps the intermediate reset reference back to the original reference. Both the Kraus term and the reset term therefore agree for every complex input matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-benchmark-reconstruction"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/LocalCompression/PetzBenchmarkDecoder.compression_recovers_benchmark"),
                H("Exact reconstruction of the ordinary benchmark"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The compression is a finite quantum channel between two joint systems with the same retained subsystem. Its action preserves the retained partial trace. The benchmark on either system is the ordinary Petz decoder of the corresponding physical partial trace, evaluated at the source marginal.")),
                    Paragraph(Text("Transitivity collapses the two reverse channels to the ordinary decoder of their forward composite. The composite acts as the original partial trace. Its Kraus adjoint is tensoring with the environment identity, which identifies its benchmark with the original one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strict-score-retention"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/LocalCompression/PetzBenchmarkDecoder.strict_score_of_decoder_residual"),
                H("Strict score retention from a decoder residual"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The source support lies in the reference support, and the score threshold is nonnegative. The score divides the squared unhalved trace norm of the source-to-benchmark difference by the supported entropy loss of the retained partial trace. Exact benchmark reconstruction and trace-norm contraction bound the compressed contrast below by the original contrast minus the measured source reconstruction error.")),
                    Paragraph(Text("The retained marginals are fixed, so supported data processing bounds the compressed entropy loss by the original loss. If the reconstruction error plus the square root of the threshold times the original loss is strictly smaller than the original contrast, the compressed contrast is positive. The supported equality criterion gives positive compressed loss and the compressed score strictly exceeds the threshold."))),
                DescribeRole.Theorem))));
}
