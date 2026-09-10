using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeGaps;

internal sealed class FragmentUniformSmoothingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/PrimeGaps/FragmentUniformSmoothing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct the independent uniform scale mixture and derive its volume domination without assuming a density bound.",
        H("Uniform Smoothing for the Fragment Mass Law"), Blocks(
            Describe.Lean(DescribeId.Create("uniform-scale-mixture"),
                DeclarationHandle.Create(Owner + "uniformScaleMixture"),
                H("An actual product-measure construction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For any real zeta and real measure nu, push nu times Lebesgue measure restricted to (0,1] forward by (s,u) mapped to u times (zeta+s). The coordinate order is residual first and uniform second. Independence is supplied by the product measure."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniform-mixture-probability"),
                DeclarationHandle.Create(Owner + "uniformScaleMixture_isProbabilityMeasure"),
                H("Probability normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every real zeta and every probability measure nu, the constructed mixture is a probability measure. This assertion requires neither positive zeta nor nonnegative residual support. The unit interval has volume exactly one and the product map is measurable."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-mixture-volume-domination"),
                DeclarationHandle.Create(Owner + "uniformScaleMixture_apply_le"),
                H("Volume domination on every measurable set"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For positive zeta, a probability measure nu supported almost surely on nonnegative reals, and any measurable set A, the mixture probability of A is at most ofReal(1/zeta) times volume(A). Condition on s. Restriction can only decrease measure, and the existing Lebesgue scaling theorem gives volume of the multiplication preimage as volume(A)/(zeta+s). Integrate the bound 1/(zeta+s) at most 1/zeta. No density, interval estimate or fixed-point identity is a premise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-mixture-half-open-interval"),
                DeclarationHandle.Create(Owner + "uniformScaleMixture_Ico_le"),
                H("An explicit interval probability"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Under the same positivity, probability and nonnegative-support conditions, every real x and delta satisfy mixture([x,x+delta)) at most ofReal(delta/zeta). The theorem includes empty intervals when delta is nonpositive. This consumes the volume-domination theorem and the existing interval-volume formula."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-fixed-point-interval"),
                DeclarationHandle.Create(Owner + "uniform_scale_fixedPoint_Ico_le"),
                H("Transfer to a law with a proved fixed-point identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The additional equality nu=uniformScaleMixture(zeta,nu) transfers the preceding interval bound to nu itself. This companion does not establish that equality for fragmentLaw. Its named downstream consumer is the fixed-mesh fragment estimate. The canonical dyadic-Poisson-to-perpetuity identity remains a separate Lean obligation."))), DescribeRole.Theorem),
            Paragraph(Text(
                "The fixed-point characterization is classical Dickman theory, as discussed by Bhattacharjee and Goldstein (arXiv:1706.08192); the scale-invariant Poisson interpretation is discussed by Bhattacharjee and Molchanov (arXiv:1911.06229). These papers provide mathematical context. This source makes no new-distribution or first-formalization claim. No kernel or emitter success is inferred from source authorship."))
        )));
}
