using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class GaussianObservationDisintegrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct actual Gaussian images and conditional laws. Formal verification status is recorded separately from these source descriptions.",
        H("GaussianObservationDisintegration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ambientcov-posdef"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationDisintegration.ambientCov_posDef"),
                H("Positive input covariance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive prior and noise precisions give a strictly positive covariance on all state and noise coordinates."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("innovation-times-cov"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationDisintegration.innovation_times_cov"),
                H("Innovation multiplied by the input covariance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Scalar precision cancellation gives an explicit two-block matrix. No covariance oracle is used."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signal-reconstruction"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationDisintegration.signal_reconstruction"),
                H("Original signal equals estimate plus innovation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original signal readout is reconstructed using the actual inverse-precision identity."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("innovation-data-covariance-zero"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationDisintegration.innovation_data_covariance_zero"),
                H("Derived innovation and data orthogonality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Zero cross covariance is proved by multiplication of the constructed matrices."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("innovation-covariance"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationDisintegration.innovation_covariance"),
                H("Innovation covariance is the inverse precision"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The reconstruction identity and zero cross covariance prove the residual covariance formula."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("input-factors"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationDisintegration.input_factors"),
                H("The actual original statistical experiment"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The input Gaussian has the specified state and noise laws and these inputs are independent."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("observation-apply"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationDisintegration.observation_apply"),
                H("The observation is M X plus independent noise"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This connects the constructed block readout to the original additive-noise experiment."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("posteriorkernel-eq-candidate"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationDisintegration.posteriorKernel_eq_candidate"),
                H("Identify the preceding Gaussian candidate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The constructed Markov kernel agrees at each data value with the inverse-precision Gaussian law from the preceding module."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("posterior-disintegration"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationDisintegration.posterior_disintegration"),
                H("Full conditional Gaussian law"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual joint law of data and signal equals the data marginal composition-product with the constructed posterior kernel. Full rank of the sensor is not assumed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("posterior-iscondkernel"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationDisintegration.posterior_isCondKernel"),
                H("Regular conditional kernel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The constructed posterior satisfies the actual Measure.IsCondKernel predicate for the original joint observation law."))), DescribeRole.Theorem))));
}
