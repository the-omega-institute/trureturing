using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class ConditionalMarkovianBenefitBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete responses factorize under coordinatewise independent-source evaluation. Sharing a random ancestor changes that premise, even when every equation has independent local noise.",
        H("Conditional factorization and shared ancestors"),
        Blocks(
            Paragraph(Text("Verification status is recorded in the unified causal partial-identification research ledger. The authored proof source is not itself evidence that the protected Lean build or maximal-catalog seal has passed.")),
            Describe.Lean(
                DescribeId.Create("conditional-joint-benefit-eq-weighted-products"),
                DeclarationHandle.Create(Prefix + "conditional_joint_benefit_eq_weighted_products"),
                H("Average the conditional products"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conditional independence gives the weighted average of stratum-specific benefit products. It does not by itself give a product of population averages."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-mixture-covariance-certificate"),
                DeclarationHandle.Create(Prefix + "binary_mixture_covariance_certificate"),
                H("Exact binary covariance certificate"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The difference between the two aggregation formulas is a rational polynomial equal to the stratum-weight product times the two conditional rate differences."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-mixture-factorizes-iff"),
                DeclarationHandle.Create(Prefix + "binary_mixture_factorizes_iff"),
                H("Exact criterion for two positive strata"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For two positive-probability strata, the population product formula holds exactly when at least one conditional mechanism benefit rate is constant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shared-root-joint-law-mass"),
                DeclarationHandle.Create(Prefix + "sharedRootJointLaw_mass"),
                H("Evaluate the explicit shared-root response law"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A fair root and two independent degenerate local disturbances push forward to equal mass on two diagonal complete-response states."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("independent-local-noise-shared-root-counterexample"),
                DeclarationHandle.Create(Prefix + "independent_local_noise_shared_root_counterexample"),
                H("Independent local noise permits dependent benefit events"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both mechanism benefit rates and their intersection equal one half in the shared-root model, whereas their marginal product equals one quarter."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shared-root-responses-do-not-factorize"),
                DeclarationHandle.Create(Prefix + "shared_root_responses_do_not_factorize"),
                H("Expose the failed componentwise-map premise"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The resulting complete response law is not a product law. The existing product-pushforward theorem remains valid because its coordinatewise-map premise does not hold for this construction."))),
                DescribeRole.Theorem))));
}
