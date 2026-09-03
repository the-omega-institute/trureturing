using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class CanonicalResponseSignatureDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/CanonicalResponseSignature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite total causal order yields finite predecessor-indexed deterministic response signatures whose event probabilities are exact linear objectives.",
        H("Canonical Causal Response Signatures"),
        Blocks(
            Paragraph(Text(
                "A total order assigns every endogenous coordinate a unique position. At position j, a canonical response table maps assignments to the j predecessor positions into the current variable's value.")),
            Paragraph(Text(
                "For finite value spaces, the dependent product of all such response tables is finite. Its probability masses therefore form a finite response-type vector.")),
            Paragraph(Text(
                "Every Boolean observational or counterfactual event on signatures has an indicator coefficient. Summing those coefficients against signature masses is exactly a rational linear objective. Pushing a finite exogenous law through its deterministic signature map preserves total mass and event probabilities.")),
            Describe.Lean(
                DescribeId.Create("node-has-unique-position"),
                DeclarationHandle.Create(Prefix + "node_has_unique_position"),
                H("Every node occupies a unique total-order position"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The inverse permutation gives the position witness, and injectivity gives uniqueness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signature-event-mass-eq-linear-objective"),
                DeclarationHandle.Create(Prefix + "signature_event_mass_eq_linearObjective"),
                H("A signature event probability is an exact linear objective"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The event indicator is zero or one on each response signature, so the finite event sum coincides term by term with linear-objective evaluation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pushforward-signature-mass-id"),
                DeclarationHandle.Create(Prefix + "pushforwardSignatureMass_id"),
                H("Every signature mass has an identity exogenous realization"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Taking the signature carrier itself as the exogenous state space and the identity as the signature map reproduces every mass exactly."))),
                DescribeRole.Theorem))));
}
