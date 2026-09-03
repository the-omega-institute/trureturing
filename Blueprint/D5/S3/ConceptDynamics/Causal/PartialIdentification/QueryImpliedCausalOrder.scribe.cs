using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class QueryImpliedCausalOrderDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/QueryImpliedCausalOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counterfactual intervention atoms generate strict causal-order obligations and expose cyclic query inconsistency.",
        H("Query-Implied Causal Order"),
        Blocks(
            Paragraph(Text(
                "A counterfactual atom names an outcome and a finite intervention set. Every nontrivial intervened coordinate generates a precedence obligation from the intervened coordinate to the atom's outcome.")),
            Paragraph(Text(
                "A query is order-compatible when one strict causal order respects every generated obligation. Asymmetry immediately rejects reciprocal requirements, which cannot occur in one recursive causal ordering.")),
            Paragraph(Text(
                "The list-order adapter targets the canonical Before relation already used by finite structural evaluation in this causal lane. LP sharpness and invariance across compatible total extensions remain separate proof obligations.")),
            Describe.Lean(
                DescribeId.Create("intervention-precedes-outcome"),
                DeclarationHandle.Create(Prefix + "intervention_precedes_outcome"),
                H("Nontrivial interventions precede their counterfactual outcomes"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The result unfolds one atom-level compiler obligation and applies the supplied query-order certificate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reciprocal-query-requirements-inconsistent"),
                DeclarationHandle.Create(Prefix + "reciprocal_query_requirements_inconsistent"),
                H("Reciprocal query-implied requirements are inconsistent"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two opposed query requirements would force both directions of one strict order, contradicting asymmetry."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("query-requirement-has-structural-before"),
                DeclarationHandle.Create(Prefix + "query_requirement_has_structural_before"),
                H("Query obligations connect to the existing structural list order"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The adapter reuses the canonical finite structural-model Before relation rather than introducing a second list-order semantics."))),
                DescribeRole.Theorem))));
}
