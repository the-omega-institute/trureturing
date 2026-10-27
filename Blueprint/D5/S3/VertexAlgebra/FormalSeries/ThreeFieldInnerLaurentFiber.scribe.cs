using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class ThreeFieldInnerLaurentFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerLaurentFiber.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite raw inner fiber", H("The finite raw inner fiber"), Blocks(
            Describe.Lean(DescribeId.Create("inner-input"),
                DeclarationHandle.Create(Prefix + "innerInput"),
                H("Signed numerator input"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonnegative r,j,l the numerator exponents are (x+a0+2k+r+j,b+k-r-l,z+a1+a2-j+l). The coefficients may be requested at arbitrary signed x,b,z."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("inner-weight"),
                DeclarationHandle.Create(Prefix + "innerWeight"),
                H("Integer-binomial weights"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The scalar is (-1)^(r+j) binom(-k,r) binom(-(2k+r),j) binom(-a1,l), using the inherited integer upper-index convention."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("inner-bounds"),
                DeclarationHandle.Create(Prefix + "inner_bounds"),
                H("Nonrectangular bounds"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonnegativity of all three numerator exponents implies r+l <= b+k and r+j <= b+z+k+a1+a2, and nonnegativity of the total shifted exponent. These bounds are proved before taking toNat."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mem-inner-fiber-iff"),
                DeclarationHandle.Create(Prefix + "mem_innerFiber_iff"),
                H("An exact finite fiber"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite containing box r,l <= (b+k).toNat and j <= (b+z+k+a1+a2).toNat is filtered by all three signed numerator constraints. Membership is equivalent to precisely those constraints. In particular, negative bounds introduce no spurious terms; P need not have finite support."))), DescribeRole.Theorem))));
}
