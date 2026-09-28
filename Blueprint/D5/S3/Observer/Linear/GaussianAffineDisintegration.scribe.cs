using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class GaussianAffineDisintegrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct actual Gaussian images and conditional laws. Formal verification status is recorded separately from these source descriptions.",
        H("GaussianAffineDisintegration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("action-adjoint"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianAffineDisintegration.action_adjoint"),
                H("Rectangular Euclidean adjoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The transpose is proved to be the Hilbert adjoint of the actual rectangular matrix action."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("action-cross-covariance"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianAffineDisintegration.action_cross_covariance"),
                H("Covariance of actual Gaussian readouts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two-readout covariance is calculated from the genuine multivariate Gaussian measure and the two actual matrices."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("map-gaussian"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianAffineDisintegration.map_gaussian"),
                H("Rectangular Gaussian pushforward"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A linear pushforward has the constructed mean and congruence covariance, including singular or blind observations."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("independent-actions"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianAffineDisintegration.independent_actions"),
                H("Independent Gaussian readouts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Zero matrix cross covariance is converted to actual independence through joint Gaussianity and the pinned covariance theorem."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("translate-gaussian"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianAffineDisintegration.translate_gaussian"),
                H("Translation of a Gaussian probability law"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The translated measure is identified from its original defining Gaussian pushforward, without an assumed normalization identity."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("translatedkernel-apply"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianAffineDisintegration.translatedKernel_apply"),
                H("A concrete affine Markov kernel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The kernel is constructed from deterministic data and a constant residual law and equals the actual translated residual measure."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("translatedkernel-compprod"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianAffineDisintegration.translatedKernel_compProd"),
                H("Affine kernel joint-law identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The composition-product of the constructed Markov kernel equals the affine pushforward of the actual product measure."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-eq-compprod-of-independent-residual"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GaussianAffineDisintegration.joint_eq_compProd_of_independent_residual"),
                H("Disintegration from independent residuals"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This measure-level lemma is applied by the observation-specific module after deriving residual independence and its distribution."))), DescribeRole.Theorem))));
}
