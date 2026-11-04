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
            Paragraph(Text("For a triangle model, let alpha, beta and gamma range over arbitrary standard Borel spaces with probability laws muAlpha, muBeta and muGamma. Use the source carrier alpha × (beta × gamma) and the law mu = muAlpha.prod (muBeta.prod muGamma). Its three own coordinate marginals are exactly the displayed factors: apply MeasureTheory.Measure.fst_prod and MeasureTheory.Measure.snd_prod at each product level. Thus the product of those own marginals is mu itself, and InformationTheory.klDiv_self gives total correlation D(mu || muAlpha × muBeta × muGamma) = 0. This argument requires neither finite sources nor uniformity, nondegeneracy or strictly positive masses.")),
            Paragraph(Text("The response maps need not preserve source independence. In the stochastic version, Alice has a measurable probability kernel K_A on the incident pair (beta, gamma), Bob has K_B on (gamma, alpha), and Charlie has K_C on (alpha, beta). The observed joint law is the integral, under that same mu, of the product of the three conditional output laws. The source KL conclusion applies to every such choice of kernels; it asserts independence of the sources and imposes no product conclusion on the output law.")),
            Paragraph(Text("To obtain an explicit triangle-local dependent law, take all three edge carriers to be Bool, gamma fair, and alpha and beta concentrated at false. Alice outputs (false, gamma), Bob outputs (false, gamma), and Charlie outputs the constant false. These are deterministic measurable kernels: Alice uses only (beta, gamma), Bob only (gamma, alpha), and Charlie only (alpha, beta). Their joint law gives mass one half to each of (((false, false), (false, false)), false) and (((false, true), (false, true)), false), and zero elsewhere.")),
            Paragraph(Text("The parameter correspondence with the existing shared-root model is exact. Permute the source coordinates by (alpha, (beta, gamma)) ↦ (gamma, (beta, alpha)); the resulting law is sharedRootSourceLaw, whose first coordinate has balancedCovariateLaw and whose two remaining coordinates have boolPointLaw false. The Alice–Bob response pair is sharedRootResponse of this permuted source. Its pushforward is therefore sharedRootJointLaw, and the triple law is that very law with a constant Charlie coordinate appended. The native finite laws use rational singleton masses; casting those masses to Real and then applying ENNReal.ofReal gives the same probability measures and the same deterministic-kernel product law, rather than a separately chosen law with matching marginals.")),
            Paragraph(Text("Under this single observed law, each of the events that Alice or Bob has second output coordinate true has probability one half, and their intersection also has probability one half. A product of their own marginals would give one quarter to that intersection. This is the triangle realization of shared_root_responses_do_not_factorize, with sharedRootJointLaw_mass and independent_local_noise_shared_root_counterexample supplying the native mass identities. The third party is constant, so dependence of the Alice–Bob marginal already prevents independence of all three outputs; no common tripartite source is used.")),
            Paragraph(Text("This construction is an application of the cited existing declarations. It establishes that independent sources allow dependent outputs. Sharing an edge alone does not force dependence: constant responses, or responses that ignore that edge, are allowed. The example does not assert a general realization theorem for arbitrary stochastic kernels, a convexity property of the full triangle image, or a resource or physical-realization claim.")),
            Describe.Lean(
                DescribeId.Create("conditional-joint-benefit-eq-weighted-products"),
                DeclarationHandle.Create(Prefix + "conditional_joint_benefit_eq_weighted_products"),
                H("Average the conditional products"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conditional independence gives the weighted average of stratum-specific benefit products. It does not by itself give a product of population averages."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-mixture-covariance-certificate"),
                DeclarationHandle.Create(Prefix + "binary_mixture_covariance_certificate"),
                H("Exact binary covariance certificate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The difference between the two aggregation formulas is a rational polynomial equal to the stratum-weight product times the two conditional rate differences."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-mixture-factorizes-iff"),
                DeclarationHandle.Create(Prefix + "binary_mixture_factorizes_iff"),
                H("Exact criterion for two positive strata"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For two positive-probability strata, the population product formula holds exactly when at least one conditional mechanism benefit rate is constant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shared-root-joint-law-mass"),
                DeclarationHandle.Create(Prefix + "sharedRootJointLaw_mass"),
                H("Evaluate the explicit shared-root response law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A fair root and two independent degenerate local disturbances push forward to equal mass on two diagonal complete-response states."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("independent-local-noise-shared-root-counterexample"),
                DeclarationHandle.Create(Prefix + "independent_local_noise_shared_root_counterexample"),
                H("Independent local noise permits dependent benefit events"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both mechanism benefit rates and their intersection equal one half in the shared-root model, whereas their marginal product equals one quarter."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shared-root-responses-do-not-factorize"),
                DeclarationHandle.Create(Prefix + "shared_root_responses_do_not_factorize"),
                H("Expose the failed componentwise-map premise"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The resulting complete response law is not a product law. The existing product-pushforward theorem remains valid because its coordinatewise-map premise does not hold for this construction."))),
                DescribeRole.Theorem))));
}
