using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal;

internal sealed class FiniteLinearCausalIdentificationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite response-type causal models compile layered assumptions and scalar queries to exact rational primal-dual certificates.",
        H("Finite Linear Causal Identification"),
        Blocks(
            Paragraph(Text(
                "The compiler target is a finite exact rational system. Response-type masses are primal variables, observational or interventional information supplies data rows, causal structure supplies structural rows, and optional sensitivity knowledge supplies separately labeled rows.")),
            Paragraph(Text(
                "Equalities can be represented by paired inequalities and probability nonnegativity by explicit rows. The query is a rational linear functional of the response-type mass vector.")),
            Paragraph(Text(
                "The semantic layer delegates arithmetic soundness to the generic linear objective certificate library. Matching rational dual and primal witnesses certify exact lower and upper causal endpoints without trusting the optimizer that discovered them.")),
            Describe.Lean(
                DescribeId.Create("query-lower-bound-of-certificate"),
                DeclarationHandle.Create(Prefix + "query_lower_bound_of_certificate"),
                H("A generic rational lower certificate proves the compiled causal bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every feasible response-type mass vector satisfies the bound after exact replay of the nonnegative row combination."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("query-upper-bound-of-certificate"),
                DeclarationHandle.Create(Prefix + "query_upper_bound_of_certificate"),
                H("A generic rational upper certificate proves the compiled causal bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The certificate checker is independent of whether a row originated from data, causal structure, or a sensitivity assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-endpoints-of-primal-dual-payload"),
                DeclarationHandle.Create(
                    Prefix + "exact_endpoints_of_primal_dual_payload"),
                H("A complete rational primal-dual payload certifies both exact causal endpoints"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two valid dual certificates and two attaining feasible response distributions close the endpoint-optimality proof obligations for a finite linear causal query."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("constraint-layer-is-exhaustive"),
                DeclarationHandle.Create(Prefix + "constraint_layer_is_exhaustive"),
                H("Every compiled row retains an auditable semantic provenance"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The layer tag makes explicit whether tightening comes from identified data, structural causal restrictions, or external sensitivity knowledge."))),
                DescribeRole.Theorem))));
}
