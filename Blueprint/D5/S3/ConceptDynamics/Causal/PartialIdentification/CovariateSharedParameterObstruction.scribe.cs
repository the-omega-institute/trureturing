using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class CovariateSharedParameterObstructionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/CovariateSharedParameterObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp covariate-stratum projections need not aggregate sharply when the strata share an unidentified structural parameter.",
        H("Covariate Shared-Parameter Obstruction"),
        Blocks(
            Paragraph(Text(
                "Two covariate strata respond in complementary ways to one common parameter. If each stratum may choose its parameter independently, each projected identified set is the full interval from zero to one.")),
            Paragraph(Text(
                "The actual joint model requires one parameter for both strata. With equal covariate weights, the two responses cancel and the global query is always one half.")),
            Paragraph(Text(
                "The value one half is forced by the affine complement involution x maps to one minus x and equal weighting. This algebraic fixed-point mechanism makes no claim about the Riemann zeta function or the location of its zeros.")),
            Paragraph(Text(
                "This construction proves that stratum-level sharpness alone is insufficient for weighted global sharpness. Joint combinability, or an equivalent product-feasibility condition, is a substantive causal assumption.")),
            Describe.Lean(
                DescribeId.Create("local-attainable-iff"),
                DeclarationHandle.Create(Prefix + "local_attainable_iff"),
                H("Each stratum projection is the exact unit interval"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For either complementary response, every value between zero and one is realized by an admissible stratum-specific parameter, and no value outside the interval is realized."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complement-fixed-point-eq-half"),
                DeclarationHandle.Create(Prefix + "complement_fixed_point_eq_half"),
                H("The affine complement involution has fixed point one half"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Solving x equals one minus x gives the unique affine midpoint. The theorem is intentionally independent of analytic number theory."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shared-parameter-attainable-iff"),
                DeclarationHandle.Create(Prefix + "shared_parameter_attainable_iff"),
                H("The shared-parameter global range is a singleton"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equal weighting of the complementary responses eliminates the common parameter and fixes the global query at one half."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shared-parameter-invalidates-naive-weighted-sharpness"),
                DeclarationHandle.Create(Prefix + "shared_parameter_invalidates_naive_weighted_sharpness"),
                H("Independent weighted sharpness can fail under cross-stratum coupling"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The independent product family realizes global value zero, while the shared-parameter family cannot. This separates projected stratum information from jointly compatible causal models."))),
                DescribeRole.Theorem))));
}
