using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CausalMoments;

internal sealed class MarkovianJointBenefitMarginalSharpBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four single-world marginals leave two internal response couplings unknown. The joint-benefit query ranges over the product of the two local sharp intervals under complete-mechanism independence.",
        H("Joint benefit from four interventional marginals"),
        Blocks(
            Paragraph(Text("Verification status is recorded in the unified causal partial-identification research ledger. The authored proof source is not itself evidence that the protected Lean build or maximal-catalog seal has passed.")),
            Describe.Lean(
                DescribeId.Create("nonnegative-product-interval-iff"),
                DeclarationHandle.Create(Prefix + "nonnegative_product_interval_iff"),
                H("Rational products fill the endpoint product interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A two-edge path in a nonnegative parameter rectangle realizes every rational target using rational factors. It does not mix two product laws."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("outcome-law-benefit-bounds"),
                DeclarationHandle.Create(Prefix + "outcomeLaw_benefit_bounds"),
                H("Recover the local benefit interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The local interval follows from the existing assignment-outcome sharpness theorem, avoiding a second four-cell necessity proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-marginal-joint-benefit-sharp-iff"),
                DeclarationHandle.Create(Prefix + "four_marginal_joint_benefit_sharp_iff"),
                H("Exact range with all four intervention marginals fixed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The theorem constructs complete response laws for every rational target between the products of the local lower and upper benefit endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("balanced-four-marginal-sharp-interval"),
                DeclarationHandle.Create(Prefix + "balanced_four_marginal_sharp_interval"),
                H("Balanced intervention marginals leave an interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When all four success marginals equal one half, every target from zero to one quarter is attained by independent complete mechanisms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-benefit-strictly-refines-four-marginal-kernel"),
                DeclarationHandle.Create(Prefix + "joint_benefit_strictly_refines_four_marginal_kernel"),
                H("A full-model observation-kernel witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two models on the existing full rational model carrier have identical four-marginal readouts and different joint-benefit values. No finite test arena or escape-rate score is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("no-joint-benefit-reconstruction-from-four-marginals"),
                DeclarationHandle.Create(Prefix + "no_joint_benefit_reconstruction_from_four_marginals"),
                H("No reconstruction from the four marginal readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The witness rules out every function that would reconstruct joint benefit from four intervention marginals on all models in this family."))),
                DescribeRole.Theorem))));
}
