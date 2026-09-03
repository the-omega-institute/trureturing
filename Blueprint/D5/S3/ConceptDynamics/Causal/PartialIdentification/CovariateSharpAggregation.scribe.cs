using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class CovariateSharpAggregationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/CovariateSharpAggregation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independently combinable covariate-stratum sharp intervals aggregate to an exact nonnegative weighted sharp interval.",
        H("Covariate Sharp Aggregation"),
        Blocks(
            Paragraph(Text(
                "Each covariate stratum supplies an exact scalar identified interval. Global attainability means that one attainable value may be selected in every stratum and combined with fixed nonnegative weights.")),
            Paragraph(Text(
                "Pointwise lower and upper bounds survive weighted summation. A common interpolation parameter simultaneously moves every stratum between its two endpoints and therefore realizes every global value between the weighted endpoints.")),
            Paragraph(Text(
                "The joint-selection premise is substantive. Shared structural parameters, transport restrictions, or other cross-stratum constraints require a different feasible family and are outside this theorem.")),
            Describe.Lean(
                DescribeId.Create("weighted-value-mono"),
                DeclarationHandle.Create(Prefix + "weightedValue_mono"),
                H("Nonnegative weights preserve pointwise stratum bounds"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Finite summation of the pointwise inequalities gives the global lower or upper bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("covariate-weighted-sharp-iff"),
                DeclarationHandle.Create(Prefix + "covariate_weighted_sharp_iff"),
                H("The weighted covariate interval is exactly sharp"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A target lies between the weighted endpoints exactly when jointly attainable stratum values aggregate to that target. Equal endpoints use a boundary witness. Distinct endpoints use one common affine interpolation parameter."))),
                DescribeRole.Theorem))));
}
