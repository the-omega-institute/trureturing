using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class GaussianPosteriorRiskDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct actual Gaussian images and conditional laws. Formal verification status is recorded separately from these source descriptions.",
        H("GaussianPosteriorRisk"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("energyloss-eq-norm"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianPosteriorRisk.energyLoss_eq_norm"),
                H("The actual Euclidean energy loss"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coordinate sum is identified with one half of the Euclidean squared norm; a different matrix or coordinate norm is not substituted."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-coordinate-square"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianPosteriorRisk.gaussian_coordinate_square"),
                H("A shifted Gaussian coordinate moment"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integral is derived from the actual coordinate mean and variance, with square integrability established."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-energy-integral"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianPosteriorRisk.gaussian_energy_integral"),
                H("Trace covariance plus mean-offset energy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Integrating the actual Gaussian probability measure gives trace covariance divided by two plus the squared offset divided by two."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-energy-lintegral"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianPosteriorRisk.gaussian_energy_lintegral"),
                H("Nonnegative conditional integration"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite Gaussian integral is transferred to ENNReal before averaging over observations."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bayesrisk-input"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianPosteriorRisk.bayesRisk_input"),
                H("Risk in the original state and noise experiment"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The joint-law loss is identified with the direct input-space expectation of the original signal and additive-noise observation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("posterior-conditional-loss"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianPosteriorRisk.posterior_conditional_loss"),
                H("Loss under the identified conditional kernel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The kernel is the constructed regular conditional law of the actual experiment, rather than a supplied posterior candidate."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bayesrisk-decomposition"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianPosteriorRisk.bayesRisk_decomposition"),
                H("Exact extended-valued risk decomposition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every measurable estimator, global risk equals the finite covariance term plus the nonnegative integrated deviation from the posterior mean. Infinite risk is retained."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("posterior-mean-attains"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianPosteriorRisk.posterior_mean_attains"),
                H("An estimator that attains the minimum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual linear posterior mean has risk exactly one half of the covariance trace."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("posterior-mean-optimal"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianPosteriorRisk.posterior_mean_optimal"),
                H("Optimality among all measurable estimators"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The lower bound includes nonlinear and infinite-risk estimators, with no integrability assumption on the competitor."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("posterior-mean-unique"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianPosteriorRisk.posterior_mean_unique"),
                H("Almost-everywhere uniqueness"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite baseline cancellation and the zero-loss identity show that equality holds exactly when the estimator equals the posterior mean almost everywhere under the data law."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bayesrisk-eq-top-iff"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianPosteriorRisk.bayesRisk_eq_top_iff"),
                H("Infinite-risk consistency"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Global risk is infinite exactly when the deviation risk is infinite. A nonintegrable loss is never assigned a zero real expectation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("futurerisk-pullback"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianPosteriorRisk.futureRisk_pullback"),
                H("Every future estimator has a present-state pullback"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse of the actual linear isometry gives a loss-preserving correspondence for arbitrary estimators."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("futurerisk-lower-bound"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianPosteriorRisk.futureRisk_lower_bound"),
                H("Optimality at every specified orthogonal future"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every measurable future-state estimator has risk at least the same covariance minimum; the transported mean attains it."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("transported-mean-risk"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianPosteriorRisk.transported_mean_risk"),
                H("Risk under known orthogonal propagation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any actual linear isometric equivalence preserves the energy loss of the transported posterior-mean estimator. No unconstructed Hamiltonian flow is assumed to be orthogonal."))), DescribeRole.Theorem))));
}
