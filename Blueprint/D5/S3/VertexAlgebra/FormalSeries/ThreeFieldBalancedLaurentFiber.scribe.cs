using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class ThreeFieldBalancedLaurentFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The numerator index", H("The numerator index"), Blocks(
            Describe.Lean(DescribeId.Create("threefieldbalancedlaurentfiber-balancedinput"),
                DeclarationHandle.Create(Prefix + "balancedInput"),
                H("The numerator index"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three natural indices r,j,l select the signed numerator exponent (s+k-r-l, x+a0+a1+2k+r+j+l, z+a2-j)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("threefieldbalancedlaurentfiber-balancedweight"),
                DeclarationHandle.Create(Prefix + "balancedWeight"),
                H("The signed binomial weight"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The weight is binom(-k,r) binom(-a0,l) (-1)^j binom(-(2k+r),j). The normalization is the integer-binomial normalization of the residue reconstruction suppliers."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("threefieldbalancedlaurentfiber-balancedfiber"),
                DeclarationHandle.Create(Prefix + "balancedFiber"),
                H("A finite fiber for every signed target"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ranges are r,l at most toNat(s+k) and j at most toNat(z+a2). All three signed numerator coordinates must be nonnegative. Negative target bounds therefore give empty admissible fibers without truncating an infinite numerator."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("threefieldbalancedlaurentfiber-balanced-bounds"),
                DeclarationHandle.Create(Prefix + "balanced_bounds"),
                H("Sharp cumulative bounds"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonnegative numerator coordinates imply r+l at most s+k, j at most z+a2 and r+j+l at most s+z+k+a2. They also force all native cumulative target degrees to be nonnegative."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("threefieldbalancedlaurentfiber-balanced-input-total"),
                DeclarationHandle.Create(Prefix + "balanced_input_total"),
                H("Constant total numerator degree"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every numerator index in the fiber has total s+x+z+3k+a0+a1+a2."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("threefieldbalancedlaurentfiber-mem-balancedfiber-iff"),
                DeclarationHandle.Create(Prefix + "mem_balancedFiber_iff"),
                H("Exact membership"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A natural triple belongs to the finite fiber exactly when all three signed numerator coordinates are nonnegative."))), DescribeRole.Theorem))));
}
