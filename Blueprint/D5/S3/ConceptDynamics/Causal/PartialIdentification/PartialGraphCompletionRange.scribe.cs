using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class PartialGraphCompletionRangeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/"
            + "PartialGraphCompletionRange.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial-graph uncertainty yields a union of completion-specific sharp ranges. "
            + "Its envelope endpoints can be exact even when the full range is disconnected.",
        H("Partial-Graph Completion Ranges"),
        Blocks(
            Paragraph(Text(
                "Each compatible complete graph carries its own sharp scalar interval. "
                    + "Under epistemic graph uncertainty, a value is attainable when at least one completion admits it.")),
            Paragraph(Text(
                "The resulting identified range is the union of completion-specific intervals. "
                    + "The smallest lower endpoint and largest upper endpoint remain exact when attained by completions.")),
            Paragraph(Text(
                "The union need not fill the envelope interval. Treating unknown graph structure as a probabilistic mixture over graph indices is an additional model assumption that can add query values.")),
            Describe.Lean(
                DescribeId.Create("partial-graph-range-is-completion-union"),
                DeclarationHandle.Create(
                    Prefix + "partial_graph_range_is_completion_union"),
                H("The partial-graph identified range is the completion union"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem identifies global attainability exactly with membership in one compatible completion's sharp interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completion-envelope-exact-endpoints"),
                DeclarationHandle.Create(
                    Prefix + "exact_lower_endpoint_of_completion_envelope"),
                H("An attained completion envelope gives an exact global endpoint"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A lower value below every completion-specific lower endpoint is globally valid, and one completion attaining it proves exactness. The module also proves the dual upper statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partial-graph-envelope-not-always-sharp"),
                DeclarationHandle.Create(
                    Prefix + "partial_graph_envelope_need_not_be_sharp_interval"),
                H("Exact envelope endpoints do not force interval sharpness"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two graph completions with singleton ranges zero and two have exact envelope endpoints, while the intermediate value one remains unattainable."))),
                DescribeRole.Theorem))));
}
