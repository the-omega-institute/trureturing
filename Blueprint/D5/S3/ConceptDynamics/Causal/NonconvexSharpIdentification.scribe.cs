using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal;

internal sealed class NonconvexSharpIdentificationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonconvex identified sets separate endpoint exactness, outer-relaxation validity, and complete range sharpness.",
        H("Nonconvex Sharp Identification"),
        Blocks(
            Paragraph(Text(
                "Polynomial cross-world restrictions can produce disconnected or otherwise nonconvex feasible families. Universal endpoint bounds and attaining endpoint models remain meaningful, while interval filling requires an additional argument.")),
            Paragraph(Text(
                "A bound established on an outer relaxation transfers to the inner model by feasible-set inclusion. Such a bound may remain loose because the relaxation can contain mixtures that violate the nonlinear restriction.")),
            Paragraph(Text(
                "The two-point example isolates the missing premise. Zero and two are exact attained endpoints, yet one is not feasible. Endpoint attainment alone therefore cannot replace convexity or a direct target-by-target construction.")),
            Describe.Lean(
                DescribeId.Create("valid-lower-bound-of-outer-relaxation"),
                DeclarationHandle.Create(
                    Prefix + "valid_lower_bound_of_outer_relaxation"),
                H("Outer-relaxation lower bounds remain valid for the inner model"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Feasible-set containment is sufficient to transfer universal validity. No convexity, topology, or attainment assumption is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("valid-upper-bound-of-outer-relaxation"),
                DeclarationHandle.Create(
                    Prefix + "valid_upper_bound_of_outer_relaxation"),
                H("Outer-relaxation upper bounds remain valid for the inner model"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the upper-bound counterpart used when a semialgebraic model is relaxed to a polyhedral or convex feasible family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-problem-exact-endpoints"),
                DeclarationHandle.Create(Prefix + "twoPointProblem_exact_endpoints"),
                H("A disconnected range can have two exact endpoints"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The feasible query range containing only zero and two has exact lower and upper endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "endpoint-attainment-without-convexity-does-not-fill-interval"),
                DeclarationHandle.Create(
                    Prefix
                        + "endpoint_attainment_without_convexity_does_not_fill_interval"),
                H("Endpoint attainment without convexity does not prove interval sharpness"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The target one lies between the two exact endpoints but has no feasible preimage, formally blocking the convex interpolation inference in nonlinear models."))),
                DescribeRole.Theorem))));
}
