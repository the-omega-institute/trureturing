using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal;

internal sealed class ConvexSharpIdentificationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/ConvexSharpIdentification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Convex feasible model families and affine queries turn attained valid endpoints into exact identified intervals.",
        H("Convex Sharp Identification"),
        Blocks(
            Paragraph(Text(
                "The logical core of scalar partial identification is independent of any particular causal graph or linear program. A feasible family, a scalar query, a convex blending operation, and affine query behavior are sufficient to state sharpness abstractly.")),
            Paragraph(Text(
                "Universal certificates and primal witnesses play different roles. A universal lower or upper bound proves validity. A feasible model attaining the same endpoint proves optimality. Convexity then fills every interior query value between two attained endpoints.")),
            Paragraph(Text(
                "Feasible-set refinement formalizes additional information. If every model satisfying stronger assumptions also satisfies weaker assumptions and the query is unchanged, valid bounds survive refinement. Exact lower endpoints can only move upward and exact upper endpoints can only move downward.")),
            Describe.Lean(
                DescribeId.Create("sharp-interval-of-valid-bounds-and-endpoint-witnesses"),
                DeclarationHandle.Create(
                    Prefix + "sharp_interval_of_valid_bounds_and_endpoint_witnesses"),
                H("Attained endpoints and convexity imply interval sharpness"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Given valid lower and upper bounds, feasible models attaining both endpoints, closure under convex blends, and affine query behavior, a target is attainable exactly when it lies between the two endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-lower-endpoint-monotone-under-refinement"),
                DeclarationHandle.Create(
                    Prefix + "exact_lower_endpoint_monotone_under_refinement"),
                H("Stronger assumptions raise exact lower endpoints"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A lower bound valid for a weaker feasible family applies to every stronger feasible model. An attaining stronger-family witness therefore cannot lie below the weaker exact lower endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-upper-endpoint-monotone-under-refinement"),
                DeclarationHandle.Create(
                    Prefix + "exact_upper_endpoint_monotone_under_refinement"),
                H("Stronger assumptions lower exact upper endpoints"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The dual information-order statement holds at the upper endpoint: an attaining stronger-family witness cannot exceed a valid weaker-family upper bound."))),
                DescribeRole.Theorem))));
}
