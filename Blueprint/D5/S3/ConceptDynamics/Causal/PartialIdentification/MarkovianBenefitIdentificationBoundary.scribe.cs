using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class MarkovianBenefitIdentificationBoundaryDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/MarkovianBenefitIdentificationBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent treatment-assignment noise leaves Boolean probability of benefit at its exact Frechet interval, while an additional factorization of the two potential-outcome response coordinates point identifies benefit.",
        H("The Markovian Boundary for Probability of Benefit"),
        Blocks(
            Paragraph(Text(
                "A standard Markovian treatment-outcome model separates the treatment-assignment disturbance from the outcome-mechanism disturbance. Both potential outcomes remain coordinates of the same outcome response type, so their cross-world dependence is unrestricted by that separation.")),
            Paragraph(Text(
                "The module constructs an explicit four-cell outcome-response law for every target in the ordinary Boolean benefit interval. Pairing that outcome law with any normalized independent assignment law produces a Markovian assignment-outcome model with the same target. Markovian assignment independence therefore does not shrink the sharp interval.")),
            Paragraph(Text(
                "A second theorem factorizes the two potential-outcome coordinates themselves. This extra cross-world restriction is stronger than standard Markovianity and forces the benefit probability to equal one minus the control success probability, multiplied by the treated success probability.")),
            Describe.Lean(
                DescribeId.Create("markovian-benefit-target-feasible-iff"),
                DeclarationHandle.Create(Prefix + "markovian_benefit_target_feasible_iff"),
                H("Markovian assignment independence preserves the exact Frechet interval"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A benefit target is realized by a product assignment-outcome response law exactly when it lies between the positive marginal difference and the smaller of treated success and control failure. Necessity uses nonnegativity and normalization. Sufficiency uses an explicit four-cell response law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("markovian-assignment-noise-does-not-point-identify-benefit"),
                DeclarationHandle.Create(
                    Prefix + "markovian_assignment_noise_does_not_point_identify_benefit"),
                H("Equal marginals admit distinct Markovian benefit probabilities"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two Markovian models have control and treated success probabilities one half. One has benefit zero and the other has benefit one half, giving a concrete machine-checked failure of point identification."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("response-coordinate-factorization-point-identifies-benefit"),
                DeclarationHandle.Create(
                    Prefix + "response_coordinate_factorization_point_identifies_benefit"),
                H("Cross-world response-coordinate factorization point identifies benefit"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When the control and treated potential-outcome coordinates are themselves product-factorized, the benefit cell is exactly the product of control failure and treated success. The theorem makes this additional assumption explicit rather than attributing it to ordinary Markovian SCM semantics."))),
                DescribeRole.Theorem))));
}
