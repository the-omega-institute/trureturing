using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class PartialGraphInformationOrderDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/PartialGraphInformationOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Required and forbidden edge information induces a contravariant order on compatible causal models and identified query values.",
        H("Partial Graph Information Order"),
        Blocks(
            Paragraph(Text(
                "A partial causal diagram records edges known to be present, edges known to be absent, and leaves every other pair unresolved. A stronger diagram retains all assertions of a weaker diagram and may add more.")),
            Paragraph(Text(
                "Compatibility is antitone in information: every complete graph satisfying the stronger diagram also satisfies the weaker one. The same inclusion transfers directly to compatible structural models and their scalar query values.")),
            Paragraph(Text(
                "The generic nonconvex identification library then transports valid bounds through the refinement. Attained stronger-family endpoints establish the expected monotonic movement of exact lower and upper bounds.")),
            Describe.Lean(
                DescribeId.Create("compatible-antitone"),
                DeclarationHandle.Create(Prefix + "compatible_antitone"),
                H("Stronger partial diagrams have fewer compatible graphs"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Required-edge and forbidden-edge inclusion are checked separately and then recombined into the weaker compatibility certificate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("identified-set-antitone"),
                DeclarationHandle.Create(Prefix + "identified_set_antitone"),
                H("Stronger graph information removes identified query values"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every stronger-family model is reused as a weaker-family witness with the same scalar query value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partial-graph-endpoint-monotonicity"),
                DeclarationHandle.Create(Prefix + "lower_endpoint_monotone_under_refinement"),
                H("Partial graph refinement raises attained lower endpoints"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A bound valid for the weaker outer family applies to an attaining witness in the stronger inner family. The companion theorem gives the reversed inequality for upper endpoints."))),
                DescribeRole.Theorem))));
}
