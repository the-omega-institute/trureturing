using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class GaussianObservationPrecisionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct actual inverse precision, complete the likelihood square and define a Gaussian measure with the resulting moments; conditional-law identification remains explicit.",
        H("Constructed Gaussian Observation Precision"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("precision-pos-def"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationPrecision.precision_posDef"),
                H("Strictly positive precision without a full-rank sensor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive prior precision and a nonnegative noise precision make beta I plus tau M-transpose M positive definite for every rectangular observation matrix, including blind or underdetermined sensors."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("precision-inverse"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationPrecision.precision_inverse"),
                H("Derive the actual inverse equations"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The covariance is the nonsingular matrix inverse of the constructed precision. Both inverse equations follow from the proved positive definiteness."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("center-equation"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationPrecision.center_equation"),
                H("Compute the Gaussian center"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse precision applied to tau M-transpose y satisfies the actual normal equation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complete-square"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationPrecision.complete_square"),
                H("Complete the prior and likelihood exponent"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The entire quadratic exponent is derived from the actual observation matrix and data. No square-completion identity is assumed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unique-quadratic-mode"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationPrecision.unique_quadratic_mode"),
                H("Unique minimizer of the exponent"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Strict positive definiteness proves the constructed center is the unique minimizer. This is a mode statement; Bayes optimality over arbitrary measurable estimators is not asserted."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exponential-kernel-factorization"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationPrecision.exponential_kernel_factorization"),
                H("Factor the genuine real exponential"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The prior-times-likelihood exponent factors into a data-only constant and the centered Gaussian quadratic. The remaining measure normalization and disintegration theorem are not hidden."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("candidate-law-mean"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationPrecision.candidateLaw_mean"),
                H("Mean of the actual candidate Gaussian measure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Uses Mathlib multivariateGaussian with the constructed mean and covariance. No arbitrary distribution is postulated."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("candidate-law-covariance"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianObservationPrecision.candidateLaw_covariance"),
                H("Actual covariance of the candidate measure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The positive inverse precision is identified with the coordinate covariance of that probability measure. Proving that this candidate equals the observation conditional law is a separate obligation."))), DescribeRole.Theorem))));
}
