using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class MarkovianResponseLawFactorizationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/MarkovianResponseLawFactorization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent finite exogenous components induce product-factorized response laws, while counterfactual event probabilities become exact linear objectives after all but one component law are fixed.",
        H("Markovian Response-Law Factorization"),
        Blocks(
            Paragraph(Text(
                "The Markovian assumption is placed at the exogenous-response level. Two normalized local response laws combine by a product mass, and coordinatewise deterministic response maps preserve that product factorization under finite pushforward.")),
            Paragraph(Text(
                "A component may represent one Markovian disturbance or an entire quasi-Markovian confounded component. Dependence inside a component remains unrestricted. Independence is asserted only across the displayed components.")),
            Paragraph(Text(
                "A Boolean counterfactual event is generally bilinear in two unknown component laws. Once the right component law is fixed, summing its event-weighted mass produces one rational coefficient for each left response state. The remaining optimization is therefore an ordinary finite linear program with exact primal-dual certificates.")),
            Paragraph(Text(
                "The global product-law family is nonconvex. Mixtures of two Markovian response laws may introduce dependence between component responses, so endpoint witnesses cannot be interpolated without an additional inner-family construction.")),
            Describe.Lean(
                DescribeId.Create("product-pushforward-factorizes"),
                DeclarationHandle.Create(Prefix + "product_pushforward_factorizes"),
                H("Componentwise deterministic pushforward preserves product factorization"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Pushing an independent product exogenous law through two coordinatewise response maps gives exactly the product of the two local response pushforwards. Every coefficient is checked by finite sum rearrangement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("independent-exogenous-components-induce-markovian-response-law"),
                DeclarationHandle.Create(
                    Prefix + "independent_exogenous_components_induce_markovian_response_law"),
                H("Independent exogenous components induce a Markovian response law"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Normalized local exogenous laws are pushed to normalized local response laws, and the preceding factorization identity packages the resulting joint response distribution as Markovian at the selected component resolution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("response-event-mass-product-eq-left-linear-objective"),
                DeclarationHandle.Create(
                    Prefix + "responseEventMass_product_eq_left_linearObjective"),
                H("Fixing one component converts a counterfactual event to a linear objective"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coefficient of a left response state is the right-law probability of all right responses that jointly satisfy the event. The full product-law event probability is exactly the resulting rational linear objective."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("response-event-bounds-of-fixed-right-certificates"),
                DeclarationHandle.Create(
                    Prefix + "response_event_bounds_of_fixed_right_certificates"),
                H("Fixed-component LP certificates bound the Markovian event probability"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Exact rational lower and upper dual certificates for the remaining component law replay directly as bounds on the original counterfactual event probability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("markovian-response-laws-not-closed-under-midpoint"),
                DeclarationHandle.Create(
                    Prefix + "markovian_response_laws_not_closed_under_midpoint"),
                H("The Markovian response-law family is globally nonconvex"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two degenerate product response laws are constructed. Their midpoint places equal mass on the two diagonal Boolean states and violates the product determinant identity, giving an exact obstruction to convex interpolation."))),
                DescribeRole.Theorem))));
}
