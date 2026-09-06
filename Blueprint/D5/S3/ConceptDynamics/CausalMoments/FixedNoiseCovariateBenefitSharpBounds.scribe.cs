using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CausalMoments;

internal sealed class FixedNoiseCovariateBenefitSharpBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The lower and upper endpoints are weighted products of the local benefit endpoints. Rational interpolation selects target values, local sharpness constructs response laws, and full tables realize every stratum simultaneously. Necessity covers arbitrary cross-row dependence.",
        H("Exact sharp interval with one fixed-noise model"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-noise-outcome"),
                DeclarationHandle.Create(Prefix + "fixedNoiseOutcome"),
                H("Treatment evaluation of a fixed response table"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Control and treatment select different coordinates of the same row of the same exogenous table."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fixed-noise-outcome-response"),
                DeclarationHandle.Create(Prefix + "fixedNoiseOutcome_response"),
                H("Complete response-pair identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two potential outcomes reproduce the selected table row exactly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-noise-stratum-model"),
                DeclarationHandle.Create(Prefix + "fixedNoiseStratumModel"),
                H("Actual row marginals in a common model"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing independent-mechanism response carrier is populated using the marginals of the two full-table laws."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("has-conditional-four-marginals"),
                DeclarationHandle.Create(Prefix + "HasConditionalFourMarginals"),
                H("Four conditional intervention marginals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The model fixes both treatment success probabilities for both mechanisms in each stratum. Values in null strata are kernel specifications."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fixed-noise-joint-benefit"),
                DeclarationHandle.Create(Prefix + "fixedNoiseJointBenefit"),
                H("Population benefit from the actual source law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sum the simultaneous-benefit cells of the common covariate and two-table pushforward law."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fixed-noise-joint-benefit-eq-weighted"),
                DeclarationHandle.Create(Prefix + "fixedNoiseJointBenefit_eq_weighted"),
                H("Weighted stratum product formula"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The population query equals the weighted sum of joint-benefit probabilities of the actual stratum response laws."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-noise-strata-simultaneously-realized"),
                DeclarationHandle.Create(Prefix + "fixedNoiseStrata_simultaneously_realized"),
                H("Discharge simultaneous stratum selection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An explicit pair of full-table disturbances realizes any finite family of independent-mechanism stratum laws."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-noise-covariate-joint-benefit-sharp-iff"),
                DeclarationHandle.Create(Prefix + "fixedNoise_covariate_joint_benefit_sharp_iff"),
                H("Exact sharp interval with one fixed-noise model"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The lower and upper endpoints are weighted products of the local benefit endpoints. Rational interpolation selects target values, local sharpness constructs response laws, and full tables realize every stratum simultaneously. Necessity covers arbitrary cross-row dependence."))),
                DescribeRole.Theorem))));
}
