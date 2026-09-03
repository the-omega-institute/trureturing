using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class AttainingStructuralModelDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/AttainingStructuralModel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite canonical response-signature probability law is realized by a structural model whose shared exogenous state indexes that complete signature.",
        H("Attaining Canonical Structural Models"),
        Blocks(
            Paragraph(Text(
                "A canonical ordered structural model has one finite exogenous carrier. Each exogenous state selects a complete deterministic response signature, and each structural equation reads the response table stored at the corresponding total-order position.")),
            Paragraph(Text(
                "Given any normalized nonnegative signature law, the signature carrier itself can serve as the exogenous state space. The identity signature map then reproduces the nominated law exactly.")),
            Paragraph(Text(
                "This construction is the primal tightness bridge. A feasible LP mass vector is converted into a finite structural witness attaining the same Boolean counterfactual event probability.")),
            Describe.Lean(
                DescribeId.Create("canonical-scm-induced-signature-mass"),
                DeclarationHandle.Create(Prefix + "canonicalSCM_inducedSignatureMass"),
                H("The canonical structural witness realizes the nominated signature law"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Identity pushforward on the signature carrier returns every mass coordinate unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("canonical-scm-structural-response"),
                DeclarationHandle.Create(Prefix + "canonicalSCM_structuralResponse"),
                H("Canonical equations are exactly the stored response tables"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At every total-order position and exogenous signature state, the structural response is definitionally the selected predecessor-response table."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("canonical-scm-attains-signature-event"),
                DeclarationHandle.Create(Prefix + "canonicalSCM_attains_signature_event"),
                H("The structural witness attains the LP event probability"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Evaluating a Boolean event on the canonical exogenous states gives the same finite sum as evaluating it on the signature-law vector."))),
                DescribeRole.Theorem))));
}
