using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class LatticeBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a>0 and original interval MemLp 2 inputs, both nearest images and all images with |m|>=2 are retained. The latter have an actual summable exponential majorant. Their combination proves absolute integrability and dominated convergence of the full image pairing as epsilon decreases to zero. The public natural-cutoff limit uses epsilon_n=1/(n+1) on the original Ioc carrier.",
        H("Actual Gamma form core: LatticeBoundary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-latticeboundary-actualiocboundarypair"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LatticeBoundary.actualIocBoundaryPair"),
                H("actualIocBoundaryPair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0 and original interval MemLp 2 inputs, both nearest images and all images with |m|>=2 are retained. The latter have an actual summable exponential majorant. Their combination proves absolute integrability and dominated convergence of the full image pairing as epsilon decreases to zero. The public natural-cutoff limit uses epsilon_n=1/(n+1) on the original Ioc carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-latticeboundary-actualiocboundarypair-nat-tendsto"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LatticeBoundary.actualIocBoundaryPair_nat_tendsto"),
                H("actualIocBoundaryPair nat tendsto"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0 and original interval MemLp 2 inputs, both nearest images and all images with |m|>=2 are retained. The latter have an actual summable exponential majorant. Their combination proves absolute integrability and dominated convergence of the full image pairing as epsilon decreases to zero. The public natural-cutoff limit uses epsilon_n=1/(n+1) on the original Ioc carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualiocboundarypair-abs-le"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LatticeBoundary.actualIocBoundaryPair_abs_le"),
                H("Uniform bound for every image and cutoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0 and every complex L2 profile on (-a,a], the absolute real boundary pairing is at most C(a) times its squared L2 norm, uniformly in the real cutoff. Here C(a)=2*pi/(1-exp(-2))+4*a*exp(-a)/((1-exp(-a))*(1-exp(-4*a))). The integral is absolutely integrable: the nearest images use the Carleman bound, and all remaining integer images use a geometric majorant."))),
                DescribeRole.Theorem))));
}
