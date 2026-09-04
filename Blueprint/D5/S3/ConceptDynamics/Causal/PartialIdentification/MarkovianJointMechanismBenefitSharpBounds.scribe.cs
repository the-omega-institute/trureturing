using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class MarkovianJointMechanismBenefitSharpBoundsDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/MarkovianJointMechanismBenefitSharpBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two mechanism-level benefit events have the full Frechet coupling interval without cross-mechanism restrictions, while independent Markovian outcome mechanisms collapse simultaneous benefit to the product of the two benefit marginals.",
        H("Sharp Joint-Benefit Bounds Across Markovian Mechanisms"),
        Blocks(
            Paragraph(Text(
                "Each outcome mechanism stores its own complete pair of control and treated potential outcomes. Dependence inside either mechanism remains unrestricted. Markovianity is imposed only between the two complete mechanism response laws.")),
            Paragraph(Text(
                "Projecting a complete response pair to its Boolean benefit status is deterministic. The product-pushforward theorem therefore shows that independent mechanism response laws induce independent benefit indicators.")),
            Paragraph(Text(
                "Without the product restriction, two benefit indicators with marginals b1 and b2 have the exact Frechet range from max of zero and b1 plus b2 minus one, to min of b1 and b2. Under independent mechanisms, simultaneous benefit is exactly b1 times b2.")),
            Describe.Lean(
                DescribeId.Create("unrestricted-joint-benefit-target-feasible-iff"),
                DeclarationHandle.Create(
                    Prefix + "unrestricted_joint_benefit_target_feasible_iff"),
                H("Unrestricted simultaneous benefit has the exact Frechet interval"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every target in the two-event Frechet interval is attained by an explicit normalized four-cell coupling of the two mechanism-level benefit indicators. Conversely, normalization and cell nonnegativity recover both endpoint inequalities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("markovian-benefit-status-pushforward-factorizes"),
                DeclarationHandle.Create(
                    Prefix + "markovian_benefit_status_pushforward_factorizes"),
                H("Benefit-status projection preserves Markovian product structure"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Pushing two independent complete outcome-mechanism response laws through their componentwise benefit indicators yields the product of the two marginal benefit-status laws. Internal potential-outcome dependence inside each mechanism is left unchanged before projection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("markovian-joint-benefit-sharp-singleton-iff"),
                DeclarationHandle.Create(
                    Prefix + "markovian_joint_benefit_sharp_singleton_iff"),
                H("Independent mechanisms point identify simultaneous benefit"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A target is realized by two independent complete outcome mechanisms with nominated marginal benefit probabilities exactly when the target equals their product. Explicit component laws provide the attaining structural witness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-joint-benefit-strict-tightening"),
                DeclarationHandle.Create(
                    Prefix + "half_joint_benefit_strict_tightening"),
                H("The half-marginal interval strictly collapses to one quarter"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When both mechanism benefit probabilities are one half, unrestricted cross-mechanism coupling admits simultaneous benefit zero and every value through one half. Every Markovian two-mechanism model instead has simultaneous benefit exactly one quarter."))),
                DescribeRole.Theorem))));
}
