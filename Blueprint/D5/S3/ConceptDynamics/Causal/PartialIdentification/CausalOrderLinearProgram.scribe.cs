using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class CausalOrderLinearProgramDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/CausalOrderLinearProgram.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical response-signature events compile to exact finite causal linear programs whose rational certificates bound the original SCM event probability.",
        H("Causal-Order Linear Programs"),
        Blocks(
            Paragraph(Text(
                "Layered observational, structural, and sensitivity constraints act on a finite response-signature mass vector. A Boolean counterfactual event supplies the objective indicator row.")),
            Paragraph(Text(
                "The compiled query equals the signature event mass exactly. Existing rational lower and upper dual certificates therefore prove bounds on the causal event itself.")),
            Paragraph(Text(
                "An exogenous structural model maps each latent state to one deterministic signature. Pushing its mass through this map preserves every Boolean event probability, giving the semantic bridge from an SCM witness to the LP variables.")),
            Describe.Lean(
                DescribeId.Create("signature-event-problem-query-eq"),
                DeclarationHandle.Create(Prefix + "signatureEventProblem_query_eq"),
                H("The compiled objective equals the signature event probability"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The compiler selects the event indicator as its objective coefficient, so equality follows from the response-signature linearity theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signature-event-upper-bound-of-certificate"),
                DeclarationHandle.Create(Prefix + "signature_event_upper_bound_of_certificate"),
                H("A rational dual certificate bounds the causal event probability"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Replaying the generic finite causal upper certificate and transporting across the objective equality yields the event bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signature-event-mass-pushforward"),
                DeclarationHandle.Create(Prefix + "signature_event_mass_pushforward"),
                H("Exogenous and response-signature event evaluations agree"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Finite sum exchange and deterministic signature assignment show that evaluating the event before or after pushforward gives the same probability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("identity-exogenous-realizes-signature-event"),
                DeclarationHandle.Create(Prefix + "identity_exogenous_realizes_signature_event"),
                H("Every finite signature-law witness has an exogenous realization"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The response-signature carrier itself serves as the latent state space, making the structural realization explicit at the law level."))),
                DescribeRole.Theorem))));
}
