using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class UmegakiSupportedMoorePenroseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/UmegakiSupportedMoorePenrose.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded arithmetic inverse tests are exactly the range-supported Moore–Penrose form.",
        H("Supported Moore–Penrose arithmetic inverse"), Blocks(
            Describe.Lean(DescribeId.Create("variationalinverse-moorepenrose"),
                DeclarationHandle.Create(Prefix + "variationalInverse_moorePenrose"),
                H("Range and maximizing preimage"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a finite positive semidefinite base Z and t in [0,1], the test values are bounded above exactly when the Hilbert–Schmidt direction belongs to the range of Aₜ = (1−t)L_Z + tR_Z. A real scaling of any complex kernel direction tests orthogonality to the kernel. Self-adjointness then gives range membership.")),
                    Paragraph(Text("On this range, complete the square about the preimage from FiniteMoorePenroseInverse. The test reaches its supremum there, and the value is the real Hilbert–Schmidt pairing of the direction with its Moore–Penrose inverse image."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("variationalinverse-output-moorepenrose"),
                DeclarationHandle.Create(Prefix + "variationalInverse_output_moorePenrose"),
                H("Range at the actual channel output"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a positive semidefinite input base and a complex direction of zero partial trace, a finite input variational form puts the amplified direction in the range of the arithmetic map of the actual amplified base. The output value is its supported Moore–Penrose pairing."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("variationalmetriccoefficient-eq-ssup-moorepenrose"),
                DeclarationHandle.Create(Prefix + "variationalMetricCoefficient_eq_sSup_moorePenrose"),
                H("Metric ratios in Moore–Penrose coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At each t in [0,1] the metric coefficient is the supremum of the same ratios with the supported Moore–Penrose numerator and faithful inverse denominator. Every admissible input in the metric ratio set supplies the required output-range membership."))),
                DescribeRole.Theorem))));
}
