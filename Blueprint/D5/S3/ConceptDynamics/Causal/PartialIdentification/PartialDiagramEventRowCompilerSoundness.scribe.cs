using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class PartialDiagramEventRowCompilerSoundnessDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/PartialDiagramEventRowCompilerSoundness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Observational, interventional, and counterfactual event probabilities compile to exact rational rows over admissible graph-completion and response-signature atoms.",
        H("Partial-Diagram Event-Row Compiler Soundness"),
        Blocks(
            Paragraph(Text(
                "The finite carrier records both a candidate graph completion and a deterministic response signature. Structural rows enforce nonnegativity, normalization, required and forbidden edge assertions, and compatibility with the query-implied causal order.")),
            Paragraph(Text(
                "Every supplied causal event is represented by a zero-one indicator on this joint carrier. Paired upper and lower rows enforce equality between its finite event mass and the nominated rational probability.")),
            Paragraph(Text(
                "Event kind and constraint provenance are stored separately. Observational, interventional, and counterfactual describe event semantics. Data, structural, and sensitivity describe why a numerical equality may be imposed.")),
            Describe.Lean(
                DescribeId.Create("feasible-iff-event-constrained-completion-law"),
                DeclarationHandle.Create(
                    Prefix + "feasible_iff_event_constrained_completion_law"),
                H("Generated rows exactly characterize admissible event-constrained laws"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A mass vector is feasible for the compiled program exactly when it is nonnegative, normalized, supported on graph completions satisfying all diagram and query-order conditions, and realizes every supplied event target."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-event-mass-pushforward"),
                DeclarationHandle.Create(Prefix + "joint_event_mass_pushforward"),
                H("Joint response pushforward preserves every Boolean event probability"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Pushing a finite exogenous law to completion-signature atoms and then evaluating an event gives exactly the probability obtained by evaluating that event directly on the original exogenous states."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compiled-event-targets-have-identity-realization"),
                DeclarationHandle.Create(
                    Prefix + "compiled_event_targets_have_identity_realization"),
                H("Every compiled event target has a canonical finite realization"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The joint atom carrier itself serves as an exogenous state space, so every feasible compiled law realizes all observational, interventional, and counterfactual event equalities in one finite model."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("feasible-antitone-under-diagram-refinement"),
                DeclarationHandle.Create(
                    Prefix + "feasible_antitone_under_diagram_refinement"),
                H("Additional partial-diagram information shrinks the event-constrained feasible set"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When a stronger partial diagram retains every assertion of a weaker diagram, every strongly feasible event law is also feasible for the weaker compiler while all statistical event rows remain unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lower-bound-survives-diagram-refinement"),
                DeclarationHandle.Create(
                    Prefix + "lower_bound_survives_diagram_refinement"),
                H("Weaker-diagram lower certificates remain valid after refinement"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A rational dual lower-bound certificate for the weaker event compiler remains valid for every mass feasible under stronger graph information. The corresponding upper-bound transport is proved symmetrically."))),
                DescribeRole.Theorem))));
}
