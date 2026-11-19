using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianSewnAnalyticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OriginalGaussianSewnAnalytic", H("Literal sewn source analytic cutoff passage"), Blocks(
            Paragraph(Text("The finite function is exp(-(rank/2)*finiteLog) times exp(effectiveConstant) times the ordinary affine coefficient of the actual effective kernel and mean. The limiting function uses gaussianLogDet, explicitEffectiveKernel, the literal left and right sourceExternal means, and the full chargeNorm*sourceConstant. The source constant retains its inverse frequency denominator. The ordinary coefficient of order m is iteratedDeriv m at zero divided by m factorial.")),
            Paragraph(Text("Normalized finite sections have norm below one throughout the unit disk. Their squared resolvent is holomorphic. The proved ordered inverse similarities express the raw inverses through this resolvent without requiring raw contraction on that disk. Finite matrix expressions and the finite polynomial formula for the affine coefficient give finite sewn holomorphy. The original finite logarithm holomorphy supplier is used directly.")),
            Paragraph(Text("The accepted uniform kernel, mean, constant and logarithm limits combine in a finite tuple. On a compact subdisk, uniform convergence bounds the eventual finite tuples inside a common compact ball. The continuous exponential and affine coefficient map is uniformly continuous on that ball, so composition gives uniform convergence of the actual sewn functions. Locally uniform derivative convergence can then be iterated to every fixed order. This does not exchange an occupation series with external coefficients and does not identify the result with the original fixed-energy source sum.")),
            D("explicitMean", "Literal limiting source means", "The left sign is -1+sourceExternal and the right sign is 1-sourceExternal."),
            D("finiteSewn", "Actual finite sewn function", "The cutoff is the original finite effective data and finite trace logarithm."),
            D("sewn", "Literal explicit limiting function", "The limiting constant is the full chargeNorm*sourceConstant, with no residual overall half."),
            D("coefficient", "Ordinary scalar Taylor coefficient", "The coefficient uses the complete factorial of its derivative order."),
            N("finiteSewn_differentiableOn", "Finite sewn holomorphy", "Every finite sewn function is holomorphic on the same open unit disk."),
            N("finiteSewn_tendstoUniformlyOn", "Uniform passage through the finite coefficient polynomial", "The actual sewn functions converge uniformly on every nonnegative closed subdisk of radius less than one."),
            N("finiteSewn_tendstoLocallyUniformlyOn", "Locally uniform literal cutoff limit", "Closed subdisks provide the neighbourhoods required for locally uniform convergence."),
            N("sewn_differentiableOn", "Holomorphy of the literal limit", "The locally uniform limit of the proved finite holomorphic functions is holomorphic."),
            N("finiteSewn_coefficient_tendsto", "Every fixed ordinary coefficient passes to the limit", "Iterate the upstream locally uniform derivative theorem, evaluate at zero, and divide by the complete factorial. Order zero is included. Application at order 2*n gives the analytic cutoff passage, while the original source identification remains a separate obligation.")), []));

    private static DocumentBlock D(string name, string title, string prose) => Node(name, title, prose, DescribeRole.Definition);
    private static DocumentBlock N(string name, string title, string prose) => Node(name, title, prose, DescribeRole.Theorem);
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("original-sewn-analytic-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
