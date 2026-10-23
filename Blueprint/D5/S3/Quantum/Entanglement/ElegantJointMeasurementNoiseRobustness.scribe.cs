using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class ElegantJointMeasurementNoiseRobustnessDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Entanglement/ElegantJointMeasurementNoiseRobustness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A true positive margin of the original inflation score gives an explicit strict box for physical EJM source noise.",
        H("Physical EJM Noise Robustness"),
        Blocks(
            Paragraph(Text("F1 and F2 are the integer coefficient functions of the actual original 16 triangle and 16 singleton blocks. Their sum is the original score on all 20 inflated nodes. A global positive score margin is a hypothesis here and must be established separately for any concrete coefficient tables.")),
            Describe.Lean(
                DescribeId.Create("actual-score-noise-expectation"),
                DeclarationHandle.Create(Prefix + "physical_score_expectation_le"),
                H("The physical noisy score has controlled local expectation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Suppose a continuous triangle response model represents the actual three-source EJM Born law at visibilities x, y and z. If every F1 coefficient has absolute value at most R, its expected full score is at most 4096 R times the complete L1 distance from the ideal endpoint.")),
                    Paragraph(Text("All 16 singleton blocks cancel because the relevant A and B marginals are exactly uniform. Every triangle block is centered against its own actual head law in ABC or BAC order. Its remaining contraction is bounded by 256 R times L1. Reindexing the complete L1 sum handles BAC order; the noisy law is not assumed symmetric when the three visibilities differ."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strict-physical-source-noise-box"),
                DeclarationHandle.Create(Prefix + "positive_score_physical_noise_box"),
                H("A true margin gives a strict box of nonlocal physical laws"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let R and m be strictly positive. Assume every actual F1 coefficient has absolute value at most R and the actual full score is at least m on every assignment of the 20 inflated nodes. Set epsilon to min(1/2, m/(24576 R)). Then epsilon is positive and every triple of source visibilities in (1-epsilon,1] gives a physical EJM triangle distribution that has no triangle-local representation.")),
                    Paragraph(Text("The physical L1 estimate gives expected score at most 8192 R times the sum of the three visibility deficits. In the strict box this is less than 24576 R epsilon, which is at most m. A positive pointwise margin would instead force the normalized local expectation to be at least m, giving a contradiction.")),
                    Paragraph(Text("The result consumes the genuine independently noisy six-qubit EJM law. It does not instantiate the positive-margin hypothesis for the pinned coefficient data, and does not substitute a global affine-noise proxy for independent sources."))),
                DescribeRole.Theorem))));
}
