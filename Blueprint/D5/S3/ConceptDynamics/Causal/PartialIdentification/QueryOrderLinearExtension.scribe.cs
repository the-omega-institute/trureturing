using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class QueryOrderLinearExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/QueryOrderLinearExtension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Certified counterfactual precedence constraints admit a complete linear extension that preserves every nontrivial query obligation.",
        H("Query-Implied Causal-Order Linear Extensions"),
        Blocks(
            Paragraph(Text(
                "A counterfactual query first emits intervention-to-outcome precedence constraints. A partial-order certificate records that these obligations are jointly acyclic and embeds them in one causal order relation.")),
            Paragraph(Text(
                "The Szpilrajn extension theorem completes that relation without deleting any certified edge. Every emitted requirement survives in the extension, while its intervention and outcome coordinates remain distinct.")),
            Paragraph(Text(
                "This result supplies an indexing order for canonical response signatures. It leaves LP soundness and invariance across alternative compatible extensions as separate theorem obligations.")),
            Describe.Lean(
                DescribeId.Create("query-requirement-source-ne-target"),
                DeclarationHandle.Create(Prefix + "query_requirement_source_ne_target"),
                H("Query-generated precedence requirements are nontrivial"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The source coordinate belongs to the intervention set and is explicitly distinct from the atom's outcome, which is the target coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("query-partial-order-has-linear-extension"),
                DeclarationHandle.Create(Prefix + "query_partial_order_has_linear_extension"),
                H("Every certified query partial order has a preserving linear extension"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The witness relation is linear, extends the full certified partial order, and preserves each query-generated intervention-to-outcome requirement together with source-target disequality."))),
                DescribeRole.Theorem))));
}
